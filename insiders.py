#!/usr/bin/env python3
"""
Insiders (Form 4, SEC) -> Telegram:
  1) TOP 5 compras de insiders, con ficha completa por empresa.
  2) ACCIONES BOMBA: 4 empresas con insiders comprando Y señales de posible
     subida fuerte (margen hasta el precio objetivo de analistas, volumen
     inusual, tendencia, resultados cercanos).

Se ejecuta automáticamente con GitHub Actions. Las claves (TELEGRAM_TOKEN,
TELEGRAM_CHAT_ID, SEC_USER_AGENT) se leen de variables de entorno (Secrets).

AVISO: son datos públicos con retraso. Nadie puede predecir qué acción va a
subir. Más potencial de subida casi siempre significa más riesgo de bajada.
No es asesoramiento financiero.
"""
import html
import os
import re
import time
import xml.etree.ElementTree as ET
from collections import defaultdict
from datetime import datetime, date
from zoneinfo import ZoneInfo

import requests

MIN_VALUE = 100_000      # compra individual mínima para contar (USD)
PAGES = 4                # páginas de 100 filings a revisar
TOP_N = 5                # top de compras
BOMB_N = 4               # máximo de "acciones bomba" a enviar
BOMB_MIN_SCORE = 4       # puntos mínimos para considerarla (si no llega, se envían menos)
BOMB_CANDIDATES = 25     # empresas con insiders que se analizan
MARKET_CANDIDATES = 40   # empresas de TODO el mercado (NYSE/NASDAQ) que se analizan
MARKET_PAGES = 3         # páginas de 250 empresas que se piden a Yahoo
BOMB_MIN_MCAP = 100_000_000   # tamaño mínimo (evita las más manipulables)
BOMB_MIN_PRICE = 1.0          # sin acciones de céntimos
BOMB_MIN_AVG_VOL = 100_000    # liquidez mínima
HEADERS = {"User-Agent": os.environ.get("SEC_USER_AGENT", "Nombre email@ejemplo.com")}
FEED = ("https://www.sec.gov/cgi-bin/browse-edgar?action=getcurrent&type=4"
        "&company=&dateb=&owner=include&start={start}&count=100&output=atom")
BOSS_WORDS = ("ceo", "chief executive", "cfo", "chief financial", "president",
              "director ejecutivo", "director general", "director financiero",
              "presidente", "consejero delegado", "director de finanzas")
_cache = {}
_tr_cache = {}
_tr_ok = {"warned": False}


def tr(text):
    """Traduce al español (Google Translate gratuito). Si falla, deja el original."""
    if not text or not str(text).strip():
        return text
    text = str(text)
    if text in _tr_cache:
        return _tr_cache[text]
    out = text
    try:
        from deep_translator import GoogleTranslator
        out = GoogleTranslator(source="auto", target="es").translate(text[:4500]) or text
    except ImportError:
        if not _tr_ok["warned"]:
            print("AVISO: falta 'deep-translator' (pip3 install deep-translator); "
                  "los textos saldrán en inglés.")
            _tr_ok["warned"] = True
    except Exception:
        pass
    _tr_cache[text] = out
    return out


def bi(text):
    """Texto en inglés (original) seguido de su traducción entre paréntesis."""
    if not text:
        return text
    es = tr(text)
    if not es or es.strip().lower() == str(text).strip().lower():
        return text
    return f"{text} ({es})"


def bi_title(title):
    """Cargo del insider: inglés + (español)."""
    fixed = {"Insider": "Directivo", "Director": "Consejero"}
    if title in fixed:
        return f"{title} ({fixed[title]})"
    return bi(title)


# ---------------------------------------------------------------- utilidades
def get(url):
    time.sleep(0.2)  # la SEC pide no pasar de 10 peticiones por segundo
    r = requests.get(url, headers=HEADERS, timeout=30)
    r.raise_for_status()
    return r


def money(x):
    return f"${x:,.0f}" if x >= 1000 else f"${x:,.2f}"


def num(x):
    return f"{x:,.0f}"


# ----------------------------------------------------------------- SEC Form 4
def recent_filings():
    """{número_de_acceso: (carpeta, enlace)}. Sin duplicados (un mismo Form 4
    aparece una vez por cada persona/empresa implicada)."""
    ns = {"a": "http://www.w3.org/2005/Atom"}
    out = {}
    for p in range(PAGES):
        feed = ET.fromstring(get(FEED.format(start=p * 100)).content)
        for e in feed.findall("a:entry", ns):
            link = e.find("a:link", ns).attrib["href"]
            folder = link.rsplit("/", 1)[0]
            acc = folder.rsplit("/", 1)[1]
            out.setdefault(acc, (folder, link))
    return out


def fetch_form4_xml(folder):
    """Descarga el filing completo (.txt) y extrae el XML del Form 4."""
    acc = folder.rsplit("/", 1)[1]
    dashed = f"{acc[:10]}-{acc[10:12]}-{acc[12:]}"
    text = get(f"{folder}/{dashed}.txt").text
    m = re.search(r"<ownershipDocument[^>]*>.*?</ownershipDocument>", text, re.S | re.I)
    if not m:
        raise ValueError("no es un Form 4 de compra/venta de acciones")
    return m.group(0).encode()


def parse_form4(xml_bytes, link):
    """Compras en mercado abierto (código P) de un Form 4."""
    root = ET.fromstring(xml_bytes)
    ticker = (root.findtext("issuer/issuerTradingSymbol") or "").strip().upper()
    company = root.findtext("issuer/issuerName", "?")
    buys = []
    for ro in root.findall("reportingOwner"):
        name = ro.findtext("reportingOwnerId/rptOwnerName", "?")
        rel = ro.find("reportingOwnerRelationship")
        is_off = rel.findtext("isOfficer") in ("1", "true")
        is_dir = rel.findtext("isDirector") in ("1", "true")
        is_10 = rel.findtext("isTenPercentOwner") in ("1", "true")
        if is_10 and not (is_off or is_dir):
            continue  # fondos/propietarios del 10%: se dejan fuera
        title = rel.findtext("officerTitle") or ("Director" if is_dir else "Insider")
        for t in root.findall("nonDerivativeTable/nonDerivativeTransaction"):
            if t.findtext("transactionCoding/transactionCode") != "P":
                continue
            try:
                sh = float(t.findtext("transactionAmounts/transactionShares/value"))
                px = float(t.findtext("transactionAmounts/transactionPricePerShare/value"))
            except (TypeError, ValueError):
                continue
            if sh * px < 1:
                continue
            try:
                total = float(t.findtext(
                    "postTransactionAmounts/sharesOwnedFollowingTransaction/value"))
            except (TypeError, ValueError):
                total = None
            buys.append(dict(
                ticker=ticker, company=company, owner=name, title=title,
                date=t.findtext("transactionDate/value", "?")[:10],
                shares=sh, price=px, value=sh * px, total=total, link=link))
    return buys


def merge_same_day(buys):
    """Une las líneas del mismo insider y el mismo día (precio medio ponderado)."""
    merged = {}
    for b in buys:
        k = (b["owner"], b["date"])
        if k not in merged:
            merged[k] = dict(b)
        else:
            m = merged[k]
            m["shares"] += b["shares"]
            m["value"] += b["value"]
            m["price"] = m["value"] / m["shares"]
            m["total"] = b["total"] if b["total"] is not None else m["total"]
    return sorted(merged.values(), key=lambda x: x["value"], reverse=True)


def score(buys):
    insiders = {b["owner"] for b in buys}
    total = sum(b["value"] for b in buys)
    s = 0
    if len(insiders) >= 2:
        s += 3
    if len(insiders) >= 3:
        s += 2
    bosses = {b["owner"] for b in buys
              if any(w in b["title"].lower() for w in BOSS_WORDS)}
    s += 2 * len(bosses)
    s += (total >= 100_000) + (total >= 500_000) + (total >= 1_000_000)
    return s, total, len(insiders)


# ------------------------------------------------- precio, empresa y noticias
def tradingview_exchange(full_name):
    n = (full_name or "").lower()
    if "nasdaq" in n:
        return "NASDAQ"
    if "nyse arca" in n or "arca" in n:
        return "NYSE ARCA"
    if "nyse" in n or "new york" in n:
        return "NYSE"
    if "amex" in n or "american" in n:
        return "AMEX"
    return None


def next_earnings(t, info, light=False):
    """Fecha de los próximos resultados (date) o None."""
    try:
        if light:
            raise ValueError
        cal = t.calendar
        ed = cal.get("Earnings Date") if isinstance(cal, dict) else None
        if ed:
            d = ed[0] if isinstance(ed, (list, tuple)) else ed
            if isinstance(d, datetime):
                d = d.date()
            if isinstance(d, date):
                return d
    except Exception:
        pass
    ts = info.get("earningsTimestamp")
    if ts:
        try:
            return datetime.fromtimestamp(ts).date()
        except Exception:
            pass
    return None


def enrich(ticker, light=False):
    """Precio, descripción, volumen, objetivo de analistas y noticias (Yahoo)."""
    key = (ticker, light)
    if key in _cache:
        return _cache[key]
    if light and (ticker, False) in _cache:
        return _cache[(ticker, False)]
    data = dict(ok=False)
    try:
        import yfinance as yf
    except ImportError:
        data["error"] = "Falta instalar yfinance (pip3 install yfinance)"
        return data
    try:
        t = yf.Ticker(ticker)
        info = t.info or {}
        data.update(
            ok=True,
            quote_type=info.get("quoteType"),
            name=info.get("longName") or info.get("shortName"),
            sector=info.get("sector"),
            industry=info.get("industry"),
            summary=info.get("longBusinessSummary"),
            price=info.get("currentPrice") or info.get("regularMarketPrice"),
            currency=info.get("currency", "USD"),
            change_pct=info.get("regularMarketChangePercent"),
            volume=info.get("regularMarketVolume") or info.get("volume"),
            avg_volume=info.get("averageVolume"),
            state=info.get("marketState"),
            exchange=info.get("fullExchangeName"),
            market_cap=info.get("marketCap"),
            target=info.get("targetMeanPrice"),
            n_analysts=info.get("numberOfAnalystOpinions"),
            high52=info.get("fiftyTwoWeekHigh"),
            ma50=info.get("fiftyDayAverage"),
            earnings=next_earnings(t, info, light),
        )
        data["isin"] = None
        heads = []
        if light:
            data["news"] = heads
            _cache[key] = data
            return data
        try:
            data["isin"] = t.isin if t.isin and t.isin != "-" else None
        except Exception:
            pass
        try:
            for item in (t.news or [])[:3]:
                c = item.get("content", item)
                title = c.get("title")
                url = (c.get("canonicalUrl") or {}).get("url") or c.get("link")
                if title:
                    heads.append((title, url))
        except Exception:
            pass
        data["news"] = heads
    except Exception as e:
        data["error"] = f"No pude obtener datos de mercado ({e.__class__.__name__})"
    _cache[key] = data
    return data


def is_stock(info):
    """True si es una acción normal (no un fondo) o si no se sabe."""
    qt = info.get("quote_type") if info.get("ok") else None
    return qt in (None, "EQUITY")


# ------------------------------------------- todo el mercado (NYSE + NASDAQ)
def market_universe():
    """Lista de acciones de EE. UU. activas hoy (Yahoo). Devuelve [símbolos]."""
    try:
        import yfinance as yf
        from yfinance import EquityQuery as EQ
    except Exception:
        return []
    quotes = []
    try:
        q = EQ("and", [
            EQ("eq", ["region", "us"]),
            EQ("is-in", ["exchange", "NMS", "NYQ"]),
            EQ("gt", ["intradaymarketcap", BOMB_MIN_MCAP]),
            EQ("gt", ["intradayprice", BOMB_MIN_PRICE]),
            EQ("gt", ["avgdailyvol3m", BOMB_MIN_AVG_VOL]),
        ])
        for page in range(MARKET_PAGES):
            r = yf.screen(q, offset=page * 250, size=250,
                          sortField="dayvolume", sortAsc=False)
            quotes += r.get("quotes", [])
    except Exception as e:
        print(f"(Buscador del mercado con filtros no disponible: {e.__class__.__name__})")
    if not quotes:
        try:  # plan B: listas ya preparadas por Yahoo
            for name in ("most_actives", "day_gainers", "small_cap_gainers",
                         "growth_technology_stocks", "undervalued_growth_stocks"):
                r = yf.screen(name, count=100)
                quotes += r.get("quotes", [])
        except Exception as e:
            print(f"(Listas de Yahoo no disponibles: {e.__class__.__name__})")
    # preselección barata: volumen de hoy frente a su media + cerca del máximo anual
    scored = {}
    for q in quotes:
        sym = (q.get("symbol") or "").upper()
        if not sym or "." in sym or "-" in sym or q.get("quoteType") not in (None, "EQUITY"):
            continue
        try:
            pre = 0.0
            vol, avg = q.get("regularMarketVolume"), q.get("averageDailyVolume3Month")
            if vol and avg:
                pre += min(vol / avg, 5)
            px, hi = q.get("regularMarketPrice"), q.get("fiftyTwoWeekHigh")
            if px and hi and px >= 0.85 * hi:
                pre += 1
            ma = q.get("fiftyDayAverage")
            if px and ma and px > ma:
                pre += 1
            scored[sym] = max(pre, scored.get(sym, 0))
        except Exception:
            continue
    ranked = sorted(scored, key=scored.get, reverse=True)
    return ranked[:MARKET_CANDIDATES]


# ------------------------------------------------------- acciones "bomba"
def bomb_eval(info, pts):
    """Devuelve (puntos, [motivos]) o None si no pasa los filtros mínimos."""
    if not (info.get("ok") and info.get("price")):
        return None
    if not is_stock(info):
        return None
    price = info["price"]
    if price < BOMB_MIN_PRICE:
        return None
    if (info.get("market_cap") or 0) < BOMB_MIN_MCAP:
        return None
    if (info.get("avg_volume") or 0) < BOMB_MIN_AVG_VOL:
        return None

    s, why = 0, []
    tgt = info.get("target")
    if tgt:
        up = (tgt / price - 1) * 100
        if up >= 50:
            s += 3
        elif up >= 25:
            s += 2
        elif up >= 10:
            s += 1
        if up >= 10:
            n = info.get("n_analysts")
            why.append(f"Objetivo medio de analistas {tgt:,.2f}: +{up:.0f}% sobre el precio"
                       + (f" ({n} analistas)" if n else ""))
    if info.get("volume") and info.get("avg_volume"):
        r = info["volume"] / info["avg_volume"]
        ch = info.get("change_pct")
        if r >= 1.5 and ch is not None and ch < -3:
            # mucho volumen con la acción cayendo: suele ser venta, no compra
            s -= 2
            why.append(f"⚠️ Volumen {r:.1f}x su media, pero cae {abs(ch):.1f}% en la última "
                       "sesión: puede ser una venta fuerte, no una subida")
        else:
            if r >= 3:
                s += 3
            elif r >= 2:
                s += 2
            elif r >= 1.5:
                s += 1
            if r >= 1.5:
                why.append(f"Volumen {r:.1f}x su media (actividad inusual)")
    hi, ma = info.get("high52"), info.get("ma50")
    if hi and price >= 0.85 * hi:
        s += 1
        why.append("Cerca de su máximo de 52 semanas (tendencia fuerte)")
    if ma and price > ma:
        s += 1
        why.append("Por encima de su media de 50 días")
    ed = info.get("earnings")
    if ed:
        days = (ed - date.today()).days
        if 0 <= days <= 21:
            s += 1
            why.append(f"Resultados el {ed.strftime('%d/%m')} (en {days} días): posible detonante")
    if pts >= 5:
        s += 2
    elif pts >= 3:
        s += 1
    return s, why


def bomb_message(rank, ticker, buys, pts, total, n_ins, info, bs, why, now_txt):
    company = buys[0]["company"] if buys else (info.get("name") or ticker)
    L = [f"💣 ACCIÓN BOMBA #{rank}:  🟢 \x01${ticker}\x02 — {company}",
         f"Puntos bomba: {bs} | Puntos insiders: {pts}", "", "⚡ POR QUÉ SALE"]
    L += [f"• {w}" for w in why]
    if buys:
        L.append(f"• {n_ins} insider(s) compraron {money(total)} en total")
    else:
        L.append("• Sin compras de insiders recientes (sale por sus señales de mercado)")

    L += ["", "🏢 QUÉ ES LA EMPRESA"]
    area = " / ".join(bi(x) for x in (info.get("sector"), info.get("industry")) if x)
    if area:
        L.append(f"Sector: {area}")
    if info.get("market_cap"):
        L.append(f"Tamaño: {money(info['market_cap'])}")
    if info.get("summary"):
        s = info["summary"].strip()
        s = (s[:300].rsplit(" ", 1)[0] + "…") if len(s) > 300 else s
        L.append(bi(s))

    L += ["", f"💵 COTIZACIÓN (a las {now_txt}, hora de España)"]
    line = f"{info['price']:,.2f} {info.get('currency', 'USD')}"
    if info.get("change_pct") is not None:
        line += f" ({info['change_pct']:+.1f}% última sesión)"
    if info.get("state") and info["state"] != "REGULAR":
        line += " — mercado cerrado: último precio"
    L.append(line)

    L += ["", "🔎 CÓMO BUSCARLA"]
    exch = tradingview_exchange(info.get("exchange"))
    L.append(f"TradingView: {exch + ':' if exch else ''}{ticker}")
    d = f"DEGIRO: busca «{ticker}»"
    if info.get("name"):
        d += f" o «{info['name']}»"
    if info.get("isin"):
        d += f" o ISIN {info['isin']}"
    L.append(d)

    L += ["", "🛒 COMPRAS DE INSIDERS"] if buys else []
    for b in buys[:3]:
        L.append(f"• {b['owner']} — {bi_title(b['title'])}: {b['date']} | Coste {money(b['price'])} | "
                 f"{num(b['shares'])} acc. | {money(b['value'])}")
    if info.get("news"):
        L += ["", "📰 NOTICIAS"]
        for title, url in info["news"][:2]:
            L.append(f"- {bi(title)}" + (f"\n  {url}" if url else ""))
    L += ["", "⚠️ Más potencial = más riesgo. Puede bajar igual de fuerte. Investiga antes."]
    return "\n".join(L)


# ------------------------------------------------------------ ficha del top 5
def company_message(rank, ticker, buys, pts, total, n_ins, info, now_txt):
    L = [f"🟢 #{rank}  \x01${ticker}\x02 — {buys[0]['company']}",
         f"Puntos: {pts} | {n_ins} insider(s) | Total comprado: {money(total)}", ""]

    L.append("🏢 QUÉ ES LA EMPRESA")
    if info.get("ok"):
        area = " / ".join(bi(x) for x in (info.get("sector"), info.get("industry")) if x)
        if area:
            L.append(f"Sector: {area}")
        if info.get("market_cap"):
            L.append(f"Tamaño (capitalización): {money(info['market_cap'])}")
        if info.get("summary"):
            s = info["summary"].strip()
            s = (s[:350].rsplit(" ", 1)[0] + "…") if len(s) > 350 else s
            L.append(bi(s))
    else:
        L.append(info.get("error", "Sin datos de la empresa"))

    L += ["", f"💵 COTIZACIÓN (a las {now_txt}, hora de España)"]
    if info.get("ok") and info.get("price"):
        ch = info.get("change_pct")
        line = f"{info['price']:,.2f} {info.get('currency', 'USD')}"
        if ch is not None:
            line += f" ({ch:+.1f}% en la última sesión)"
        if info.get("state") and info["state"] != "REGULAR":
            line += " — mercado cerrado: último precio disponible"
        L.append(line)
        if info.get("volume") and info.get("avg_volume"):
            ratio = info["volume"] / info["avg_volume"]
            L.append(f"Volumen vs. su media: {ratio:.1f}x"
                     + (" (actividad inusual)" if ratio >= 2 else ""))
    else:
        L.append("No disponible")

    L += ["", "🔎 CÓMO BUSCARLA"]
    exch = tradingview_exchange(info.get("exchange")) if info.get("ok") else None
    L.append(f"TradingView: {exch + ':' if exch else ''}{ticker}")
    degiro = f"DEGIRO: busca «{ticker}»"
    if info.get("ok") and info.get("name"):
        degiro += f" o el nombre «{info['name']}»"
    if info.get("isin"):
        degiro += f" o el ISIN {info['isin']}"
    L.append(degiro + " (comprueba que sea la bolsa de EE. UU.)")

    L += ["", "🛒 COMPRAS DE INSIDERS"]
    for b in buys[:5]:
        L.append(f"• {b['owner']} — {bi_title(b['title'])}")
        tot = f" | Acciones totales: {num(b['total'])}" if b["total"] else ""
        L.append(f"  {b['date']} | Compra | Coste: {money(b['price'])} | "
                 f"Acciones: {num(b['shares'])} | Valor: {money(b['value'])}{tot}")
        L.append(f"  Form 4: {b['link']}")

    if info.get("ok") and info.get("news"):
        L += ["", "📰 NOTICIAS RECIENTES"]
        for title, url in info["news"][:3]:
            L.append(f"- {bi(title)}" + (f"\n  {url}" if url else ""))
    return "\n".join(L)


# ------------------------------------------------------------------- envío
def send_telegram(text):
    token = os.environ.get("TELEGRAM_TOKEN")
    chat = os.environ.get("TELEGRAM_CHAT_ID")
    if not token or not chat:
        return
    body = html.escape(text[:3500]).replace("\x01", "<b>").replace("\x02", "</b>")
    requests.post(f"https://api.telegram.org/bot{token}/sendMessage",
                  json={"chat_id": chat, "text": body, "parse_mode": "HTML",
                        "disable_web_page_preview": True}, timeout=30)


def emit(text):
    shown = text.replace("\x01", "\033[1;92m").replace("\x02", "\033[0m")
    print("\n" + "=" * 60 + "\n" + shown)
    send_telegram(text)


def main():
    now_txt = datetime.now(ZoneInfo("Europe/Madrid")).strftime("%d/%m %H:%M")
    filings = recent_filings()
    print(f"Revisando {len(filings)} Form 4 únicos de la SEC...")
    by_ticker = defaultdict(list)
    skipped = defaultdict(int)
    for n_f, (acc, (folder, link)) in enumerate(filings.items(), 1):
        if n_f % 50 == 0:
            print(f"  ...{n_f}/{len(filings)}")
        try:
            for b in parse_form4(fetch_form4_xml(folder), link):
                if b["ticker"] and b["ticker"] not in ("NONE", "N/A") \
                        and b["value"] >= MIN_VALUE:
                    by_ticker[b["ticker"]].append(b)
        except ValueError:
            skipped["sin compras/ventas de acciones"] += 1
        except Exception as e:
            skipped[e.__class__.__name__] += 1
    if skipped:
        print("No se usaron:", dict(skipped))

    ranked = sorted(((score(v), tk, merge_same_day(v)) for tk, v in by_ticker.items()),
                    key=lambda x: (x[0][0], x[0][1]), reverse=True)
    if not ranked:
        emit("Hoy no encontré compras de insiders que pasen el filtro.")

    # ---- TOP 5 (sin fondos)
    top, used = [], set()
    for item in ranked[:TOP_N * 3]:
        if len(top) >= TOP_N:
            break
        info = enrich(item[1])
        if is_stock(info):
            top.append((item, info))
            used.add(item[1])

    if top:
        send_telegram(f"🏆 TOP {len(top)} COMPRAS DE INSIDERS — {now_txt} (España)\n"
                      "Datos públicos de la SEC, con retraso. Sirve para investigar, "
                      "no es una recomendación de compra.")
    print(f"\n🏆 TOP {len(top)} COMPRAS DE INSIDERS — {now_txt}")
    for n, (((pts, total, n_ins), tk, buys), info) in enumerate(top, 1):
        emit(company_message(n, tk, buys, pts, total, n_ins, info, now_txt))

    # ---- ACCIONES BOMBA
    print("\nBuscando acciones bomba...")
    bombs, seen = [], set()
    for (pts, total, n_ins), tk, buys in ranked[:BOMB_CANDIDATES]:
        if tk in used:
            continue
        seen.add(tk)
        ev = bomb_eval(enrich(tk, light=True), pts)
        if ev:
            bombs.append((ev[0], pts, total, n_ins, tk, buys, ev[1]))
    market = market_universe()
    print(f"Empresas del mercado analizadas: {len(market)}")
    for tk in market:
        if tk in seen or tk in used:
            continue
        ev = bomb_eval(enrich(tk, light=True), 0)
        if ev:
            bombs.append((ev[0], 0, 0, 0, tk, [], ev[1]))
    bombs = [b for b in bombs if b[0] >= BOMB_MIN_SCORE]
    bombs.sort(key=lambda x: (x[0], x[1]), reverse=True)
    bombs = bombs[:BOMB_N]

    if bombs:
        send_telegram(f"💣 ACCIONES BOMBA — {now_txt} (España)\n"
                      "Mejores señales de posible subida fuerte entre las acciones de NYSE y "
                      "NASDAQ (con o sin insiders comprando). "
                      "Alto potencial = alto riesgo. No es una recomendación.")
        for n, (bs, pts, total, n_ins, tk, buys, why) in enumerate(bombs, 1):
            full = enrich(tk)  # ficha completa (noticias, ISIN) solo de las elegidas
            ev = bomb_eval(full, pts) or (bs, why)
            emit(bomb_message(n, tk, buys, pts, total, n_ins, full,
                              ev[0], ev[1], now_txt))
    else:
        emit("💣 ACCIONES BOMBA: hoy ninguna empresa reúne suficientes señales "
             "(mejor no forzar nada).")


if __name__ == "__main__":
    main()
