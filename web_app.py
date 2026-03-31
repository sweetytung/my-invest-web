from flask import Flask, request, render_template_string
import math
import difflib
import os
from typing import Tuple, Optional
from urllib.parse import quote
from urllib.request import Request, urlopen
import xml.etree.ElementTree as ET
import html

import numpy as np
import pandas as pd
import yfinance as yf
import twstock
import plotly.graph_objects as go
from plotly.subplots import make_subplots

app = Flask(__name__)

KEYWORD_MAP = {
    "美元": "USDTWD=X", "美元兌台幣": "USDTWD=X", "usd/twd": "USDTWD=X",
    "澳幣": "AUDTWD=X", "澳幣兌台幣": "AUDTWD=X", "aud/twd": "AUDTWD=X",
    "日圓": "JPYTWD=X", "日幣": "JPYTWD=X", "jpy/twd": "JPYTWD=X",
    "歐元": "EURTWD=X", "eur/twd": "EURTWD=X",
    "美債": "TLT", "20年美債": "TLT", "長天期美債": "TLT", "7-10年美債": "IEF",
    "中天期美債": "IEF", "短債": "SHY", "投等債": "LQD", "投資等級債": "LQD",
    "非投等債": "HYG", "高收益債": "HYG", "總體債券": "BND", "新興市場債": "EMB",
    "台灣加權指數": "^TWII", "台股加權指數": "^TWII", "台灣加權": "^TWII",
    "加權指數": "^TWII", "台股大盤": "^TWII", "大盤": "^TWII", "twii": "^TWII",
    "黃金": "GC=F", "金價": "GC=F", "gold": "GC=F", "白銀": "SI=F", "銀價": "SI=F",
    "silver": "SI=F", "白金": "PL=F", "platinum": "PL=F", "鈀金": "PA=F",
    "palladium": "PA=F", "原油": "CL=F", "紐約原油": "CL=F", "美國原油": "CL=F",
    "crude oil": "CL=F", "oil": "CL=F", "布蘭特原油": "BZ=F", "brent": "BZ=F",
    "天然氣": "NG=F", "natural gas": "NG=F", "銅": "HG=F", "copper": "HG=F",
    "玉米": "ZC=F", "corn": "ZC=F", "黃豆": "ZS=F", "大豆": "ZS=F",
    "soybean": "ZS=F", "小麥": "ZW=F", "wheat": "ZW=F", "咖啡": "KC=F",
    "coffee": "KC=F", "可可": "CC=F", "cocoa": "CC=F", "棉花": "CT=F", "cotton": "CT=F",
    "蘋果": "AAPL", "apple": "AAPL", "微軟": "MSFT", "microsoft": "MSFT", "輝達": "NVDA",
    "英偉達": "NVDA", "nvidia": "NVDA", "亞馬遜": "AMZN", "amazon": "AMZN",
    "谷歌": "GOOGL", "google": "GOOGL", "alphabet": "GOOGL", "特斯拉": "TSLA",
    "tesla": "TSLA", "meta": "META", "臉書": "META", "facebook": "META", "波克夏": "BRK-B",
    "berkshire": "BRK-B", "spy": "SPY", "標普500": "SPY", "標普500etf": "SPY",
    "qqq": "QQQ", "nasdaq100": "QQQ", "那斯達克100": "QQQ", "dia": "DIA",
    "道瓊etf": "DIA", "soxx": "SOXX", "半導體etf": "SOXX", "vti": "VTI",
    "美股大盤etf": "VTI", "voo": "VOO",
    "匯豐": "HSBA.L", "匯豐控股": "HSBA.L", "hsbc": "HSBA.L", "hsba": "HSBA.L",
    "英國石油": "BP.L", "bp": "BP.L", "沃達豐": "VOD.L", "vodafone": "VOD.L",
    "vod": "VOD.L", "巴克萊": "BARC.L", "barclays": "BARC.L", "barc": "BARC.L",
    "勞斯萊斯": "RR.L", "勞斯萊斯控股": "RR.L", "rolls royce": "RR.L", "rr": "RR.L",
    "聯合利華": "ULVR.L", "unilever": "ULVR.L", "ulvr": "ULVR.L", "英美資源": "AAL.L",
    "anglo american": "AAL.L", "aal": "AAL.L", "阿斯特捷利康": "AZN.L", "astrazeneca": "AZN.L",
    "力拓英股": "RIO.L", "rio tinto": "RIO.L", "rio": "RIO.L",
}

BOND_SYMBOLS = {"TLT", "IEF", "SHY", "LQD", "HYG", "BND", "EMB"}
INDEX_SYMBOLS = {"^TWII"}
COMMODITY_SYMBOLS = {"GC=F", "SI=F", "PL=F", "PA=F", "CL=F", "BZ=F", "NG=F", "HG=F", "ZC=F", "ZS=F", "ZW=F", "KC=F", "CC=F", "CT=F"}

TW_NAME_MAP = {}
TW_CODE_MAP = {}
TW_ALIAS_MAP = {}
TW_NAME_LIST = []

UK_COMPANY_ALIASES = {
    "HSBA.L": ["匯豐", "匯豐控股", "HSBC", "HSBA", "HSBC HOLDINGS", "HSBC HOLDINGS PLC"],
    "BP.L": ["英國石油", "BP", "BP PLC"],
    "VOD.L": ["沃達豐", "VODAFONE", "VODAFONE GROUP", "VOD", "VODAFONE GROUP PLC"],
    "BARC.L": ["巴克萊", "BARCLAYS", "BARC", "BARCLAYS PLC"],
    "RR.L": ["勞斯萊斯", "勞斯萊斯控股", "ROLLS ROYCE", "ROLLS-ROYCE", "ROLLS ROYCE HOLDINGS", "RR"],
    "ULVR.L": ["聯合利華", "UNILEVER", "ULVR", "UNILEVER PLC"],
    "AAL.L": ["英美資源", "ANGLO AMERICAN", "AAL", "ANGLO AMERICAN PLC"],
    "AZN.L": ["阿斯特捷利康", "ASTRAZENECA", "AZN", "ASTRAZENECA PLC"],
    "RIO.L": ["力拓", "力拓英股", "RIO TINTO", "RIO", "RIO TINTO PLC"],
    "GLEN.L": ["嘉能可", "GLENCORE", "GLEN", "GLENCORE PLC"],
    "LLOY.L": ["勞埃德銀行", "LLOYDS", "LLOYDS BANKING GROUP", "LLOY", "LLOYDS BANKING GROUP PLC"],
    "SHEL.L": ["殼牌", "SHELL", "SHEL", "SHELL PLC"],
    "GSK.L": ["葛蘭素史克", "GSK", "GLAXOSMITHKLINE", "GSK PLC"],
    "NG.L": ["英國國家電網", "NATIONAL GRID", "NG", "NATIONAL GRID PLC"],
    "DGE.L": ["帝亞吉歐", "DIAGEO", "DGE", "DIAGEO PLC"],
}
UK_NAME_MAP = {}
UK_NAME_LIST = []


def normalize_name_text(text: str) -> str:
    if not text:
        return ""
    return str(text).strip().replace(" ", "").replace("　", "").upper()


def market_to_yf_suffix(market: str) -> str:
    market = str(market).strip()
    if market == "上市":
        return ".TW"
    if market == "上櫃":
        return ".TWO"
    return ""


def build_twstock_maps() -> None:
    global TW_NAME_MAP, TW_CODE_MAP, TW_ALIAS_MAP, TW_NAME_LIST
    name_map, code_map, alias_map = {}, {}, {}
    for _, info in twstock.codes.items():
        try:
            stock_code = str(info.code).strip()
            stock_name = str(info.name).strip()
            market = str(info.market).strip()
            sec_type = str(info.type).strip()
            if market not in {"上市", "上櫃"}:
                continue
            if sec_type not in {"股票", "ETF", "ETN", "受益憑證"}:
                continue
            suffix = market_to_yf_suffix(market)
            if not suffix:
                continue
            yf_symbol = f"{stock_code}{suffix}"
            norm_name = normalize_name_text(stock_name)
            norm_code = normalize_name_text(stock_code)
            if norm_name:
                name_map[norm_name] = yf_symbol
            code_map[norm_code] = yf_symbol
            alias_map[norm_name] = yf_symbol
            alias_map[norm_code] = yf_symbol
            short_name = stock_name.replace("股份有限公司", "").replace("有限公司", "").strip()
            norm_short_name = normalize_name_text(short_name)
            if norm_short_name:
                alias_map[norm_short_name] = yf_symbol
            if "台灣積體電路" in stock_name or stock_name == "台積電":
                alias_map["台積電"] = yf_symbol
                alias_map["台積"] = yf_symbol
                alias_map["TSMC"] = yf_symbol
            if stock_name == "元大台灣50":
                alias_map["台灣50"] = yf_symbol
                alias_map["元大50"] = yf_symbol
                alias_map["0050"] = yf_symbol
            if stock_name == "中華電":
                alias_map["中華電信"] = yf_symbol
        except Exception:
            continue
    TW_NAME_MAP = name_map
    TW_CODE_MAP = code_map
    TW_ALIAS_MAP = alias_map
    TW_NAME_LIST = sorted(set(list(name_map.keys()) + list(alias_map.keys())))


build_twstock_maps()


def build_uk_name_maps() -> None:
    global UK_NAME_MAP, UK_NAME_LIST
    alias_map = {}
    for symbol, aliases in UK_COMPANY_ALIASES.items():
        for alias in aliases:
            norm = normalize_name_text(alias)
            if norm:
                alias_map[norm] = symbol
    UK_NAME_MAP = alias_map
    UK_NAME_LIST = sorted(alias_map.keys())


build_uk_name_maps()


def resolve_uk_stock_symbol(query: str):
    q = normalize_name_text(query)
    if not q:
        return None
    if q in UK_NAME_MAP:
        return {"symbol": UK_NAME_MAP[q]}
    contains_matches = [name for name in UK_NAME_LIST if q in name]
    if len(contains_matches) == 1:
        return {"symbol": UK_NAME_MAP[contains_matches[0]]}
    fuzzy = difflib.get_close_matches(q, UK_NAME_LIST, n=5, cutoff=0.65)
    if len(fuzzy) == 1:
        return {"symbol": UK_NAME_MAP[fuzzy[0]]}
    return None


def suggest_uk_stock_names(query: str, limit: int = 5):
    q = normalize_name_text(query)
    if not q:
        return []
    contains_matches = [name for name in UK_NAME_LIST if q in name][:limit]
    if contains_matches:
        return contains_matches
    return difflib.get_close_matches(q, UK_NAME_LIST, n=limit, cutoff=0.4)


def safe_float(x, digits: int = 2):
    try:
        if pd.isna(x):
            return None
        return round(float(x), digits)
    except Exception:
        return None


def calc_rsi(series: pd.Series, period: int = 14) -> pd.Series:
    delta = series.diff()
    gain = delta.clip(lower=0)
    loss = -delta.clip(upper=0)
    avg_gain = gain.ewm(alpha=1 / period, min_periods=period, adjust=False).mean()
    avg_loss = loss.ewm(alpha=1 / period, min_periods=period, adjust=False).mean()
    rs = avg_gain / avg_loss.replace(0, pd.NA)
    return 100 - (100 / (1 + rs))


def calc_kd(hist: pd.DataFrame, period: int = 9, k_smooth: int = 3, d_smooth: int = 3):
    low_min = hist["Low"].rolling(window=period, min_periods=period).min()
    high_max = hist["High"].rolling(window=period, min_periods=period).max()
    spread = (high_max - low_min).replace(0, pd.NA)
    rsv = ((hist["Close"] - low_min) / spread) * 100
    k = rsv.ewm(alpha=1 / k_smooth, adjust=False).mean()
    d = k.ewm(alpha=1 / d_smooth, adjust=False).mean()
    return k, d


def calc_bollinger(close: pd.Series, window: int = 20, num_std: float = 2.0):
    mid = close.rolling(window).mean()
    std = close.rolling(window).std()
    upper = mid + num_std * std
    lower = mid - num_std * std
    width = ((upper - lower) / mid.replace(0, pd.NA)) * 100
    return mid, upper, lower, width


def calc_atr(hist: pd.DataFrame, period: int = 14):
    high = hist["High"]
    low = hist["Low"]
    close = hist["Close"]
    prev_close = close.shift(1)
    tr = pd.concat([
        high - low,
        (high - prev_close).abs(),
        (low - prev_close).abs(),
    ], axis=1).max(axis=1)
    return tr.rolling(period).mean()


def resolve_tw_stock_symbol(query: str):
    q = normalize_name_text(query)
    if not q:
        return None
    if q in TW_ALIAS_MAP:
        return {"symbol": TW_ALIAS_MAP[q]}
    if q in TW_NAME_MAP:
        return {"symbol": TW_NAME_MAP[q]}
    if q in TW_CODE_MAP:
        return {"symbol": TW_CODE_MAP[q]}
    contains_matches = [name for name in TW_NAME_LIST if q in name]
    if len(contains_matches) == 1:
        hit = contains_matches[0]
        symbol = TW_ALIAS_MAP.get(hit) or TW_NAME_MAP.get(hit)
        if symbol:
            return {"symbol": symbol}
    fuzzy = difflib.get_close_matches(q, TW_NAME_LIST, n=5, cutoff=0.6)
    if len(fuzzy) == 1:
        hit = fuzzy[0]
        symbol = TW_ALIAS_MAP.get(hit) or TW_NAME_MAP.get(hit)
        if symbol:
            return {"symbol": symbol}
    return None


def suggest_tw_stock_names(query: str, limit: int = 5):
    q = normalize_name_text(query)
    if not q:
        return []
    contains_matches = [name for name in TW_NAME_LIST if q in name][:limit]
    if contains_matches:
        return contains_matches
    return difflib.get_close_matches(q, TW_NAME_LIST, n=limit, cutoff=0.4)


def get_chinese_name(query: str, symbol: str, asset_type: str) -> str:
    if symbol.endswith(".TW") or symbol.endswith(".TWO"):
        code = symbol.split(".")[0]
        info = twstock.codes.get(code)
        if info and getattr(info, "name", None):
            return str(info.name).strip()
    fx_name_map = {
        "USDTWD=X": "美元兌台幣", "AUDTWD=X": "澳幣兌台幣", "JPYTWD=X": "日圓兌台幣", "EURTWD=X": "歐元兌台幣",
    }
    index_name_map = {"^TWII": "台灣加權指數"}
    bond_name_map = {
        "TLT": "20年美債 ETF", "IEF": "7-10年美債 ETF", "SHY": "短天期美債 ETF", "LQD": "投資等級債 ETF",
        "HYG": "高收益債 ETF", "BND": "總體債券 ETF", "EMB": "新興市場債 ETF",
    }
    commodity_name_map = {
        "GC=F": "黃金", "SI=F": "白銀", "PL=F": "白金", "PA=F": "鈀金", "CL=F": "紐約原油",
        "BZ=F": "布蘭特原油", "NG=F": "天然氣", "HG=F": "銅", "ZC=F": "玉米", "ZS=F": "黃豆",
        "ZW=F": "小麥", "KC=F": "咖啡", "CC=F": "可可", "CT=F": "棉花",
    }
    stock_name_map = {
        "AAPL": "蘋果", "MSFT": "微軟", "NVDA": "輝達", "AMZN": "亞馬遜", "GOOGL": "谷歌", "TSLA": "特斯拉",
        "META": "Meta", "BRK-B": "波克夏", "SPY": "標普500 ETF", "QQQ": "那斯達克100 ETF", "DIA": "道瓊 ETF",
        "SOXX": "半導體 ETF", "VTI": "美股大盤 ETF", "VOO": "先鋒標普500 ETF", "HSBA.L": "匯豐控股",
        "BP.L": "英國石油", "VOD.L": "沃達豐", "BARC.L": "巴克萊", "RR.L": "勞斯萊斯", "ULVR.L": "聯合利華",
        "AAL.L": "英美資源", "AZN.L": "阿斯特捷利康", "RIO.L": "力拓",
    }
    for mp in [fx_name_map, index_name_map, bond_name_map, commodity_name_map, stock_name_map]:
        if symbol in mp:
            return mp[symbol]
    return query


def normalize_symbol(query: str, market_scope: str = "auto") -> str:
    q = query.strip()
    q_lower = q.lower()
    if q_lower in KEYWORD_MAP:
        return KEYWORD_MAP[q_lower]
    if q in KEYWORD_MAP:
        return KEYWORD_MAP[q]
    q_upper = q.upper()
    if q_upper.endswith((".TW", ".TWO", ".L", "=X")) or q_upper.startswith("^"):
        return q_upper
    if market_scope == "tw":
        resolved = resolve_tw_stock_symbol(q)
        if resolved:
            return resolved["symbol"]
        if q.isdigit():
            return f"{q}.TW"
    if market_scope == "uk":
        resolved_uk = resolve_uk_stock_symbol(q)
        if resolved_uk:
            return resolved_uk["symbol"]
        if q_upper.endswith(".L"):
            return q_upper
        if q_upper.isalpha():
            return f"{q_upper}.L"
        return q_upper
    if market_scope == "us":
        return q_upper.replace(".L", "")
    resolved = resolve_tw_stock_symbol(q)
    if resolved:
        return resolved["symbol"]
    resolved_uk = resolve_uk_stock_symbol(q)
    if resolved_uk:
        return resolved_uk["symbol"]
    if q.isdigit():
        return f"{q}.TW"
    return q_upper


def is_likely_global_ticker_query(query: str) -> bool:
    q = (query or "").strip().upper().replace(".L", "")
    if not q or len(q) > 5:
        return False
    return q.isalpha()


def resolve_market_aware_symbol(query: str, market_scope: str = "auto"):
    symbol = normalize_symbol(query, market_scope=market_scope)
    if market_scope in {"tw", "us", "uk"}:
        return {"symbol": symbol, "message": None}

    q = (query or "").strip()
    if not is_likely_global_ticker_query(q):
        return {"symbol": symbol, "message": None}

    us_symbol = normalize_symbol(q, market_scope="us")
    uk_symbol = normalize_symbol(q, market_scope="uk")

    us_hist, us_real = get_history(us_symbol)
    uk_hist, uk_real = get_history(uk_symbol)
    us_ok = not us_hist.empty and len(us_hist) >= 70
    uk_ok = not uk_hist.empty and len(uk_hist) >= 70

    if us_ok and uk_ok:
        return {
            "symbol": None,
            "message": f"代號「{q.upper()}」同時可能是美股與英股，為避免查錯市場，請改用上方『市場選項』指定查詢。<br>• 美股：{us_real}<br>• 英股：{uk_real}"
        }
    if uk_ok and not us_ok:
        return {"symbol": uk_real, "message": None}
    if us_ok and not uk_ok:
        return {"symbol": us_real, "message": None}
    return {"symbol": symbol, "message": None}


def detect_asset_type(query: str, symbol: str, market_scope: str = "auto") -> str:
    q = query.strip().lower()
    if symbol in INDEX_SYMBOLS or any(x in q for x in ["加權指數", "台股大盤", "大盤", "台灣加權"]):
        return "index"
    if symbol.endswith("=X") or any(x in q for x in ["美元", "澳幣", "日圓", "日幣", "歐元"]):
        return "fx"
    if symbol in COMMODITY_SYMBOLS or any(k in query for k in ["黃金", "白銀", "原油", "天然氣", "銅", "玉米", "黃豆", "大豆", "小麥", "咖啡", "可可", "棉花", "白金", "鈀金"]):
        return "commodity"
    if any(k in query for k in ["美債", "投等債", "投資等級債", "非投等債", "高收益債", "新興市場債", "債"]) or symbol in BOND_SYMBOLS:
        return "bond"
    if market_scope == "uk" or symbol.endswith(".L"):
        return "uk_stock"
    if market_scope == "tw" or symbol.endswith((".TW", ".TWO")):
        return "stock"
    return "us_stock"


def get_history(symbol: str) -> Tuple[pd.DataFrame, str]:
    ticker = yf.Ticker(symbol)
    hist = ticker.history(period="1y", interval="1d", auto_adjust=False)
    if (hist.empty or len(hist) < 70) and symbol.endswith(".TW"):
        alt = symbol.replace(".TW", ".TWO")
        ticker = yf.Ticker(alt)
        hist_alt = ticker.history(period="1y", interval="1d", auto_adjust=False)
        if not hist_alt.empty and len(hist_alt) >= 70:
            return hist_alt, alt
    return hist, symbol


def estimate_dividend_yield(symbol: str, current_price: Optional[float]) -> Optional[float]:
    if current_price is None or current_price <= 0:
        return None
    try:
        ticker = yf.Ticker(symbol)
        dividends = ticker.dividends
        if dividends is None or len(dividends) == 0:
            return None
        dividends = dividends.dropna()
        if len(dividends) == 0:
            return None
        last_date = dividends.index.max()
        one_year_before = last_date - pd.Timedelta(days=365)
        annual_div = dividends[dividends.index > one_year_before].sum()
        if pd.isna(annual_div) or annual_div <= 0:
            return None
        return round(float(annual_div) / float(current_price) * 100, 2)
    except Exception:
        return None


def pick_first_valid_series(df: Optional[pd.DataFrame], candidates: list[str]) -> Optional[pd.Series]:
    if df is None or getattr(df, "empty", True):
        return None
    for col in candidates:
        if col in df.index:
            s = pd.to_numeric(df.loc[col], errors="coerce").dropna()
            if not s.empty:
                return s
    return None


def get_fundamental_metrics(symbol: str, asset_type: str):
    if asset_type not in {"stock", "us_stock", "uk_stock"}:
        return None
    try:
        ticker = yf.Ticker(symbol)
        q_income = getattr(ticker, "quarterly_income_stmt", None)
        if q_income is None or q_income.empty:
            return None
        revenue = pick_first_valid_series(q_income, ["Total Revenue", "Operating Revenue", "Revenue"])
        operating_income = pick_first_valid_series(q_income, ["Operating Income", "EBIT"])
        net_income = pick_first_valid_series(q_income, ["Net Income", "Net Income Common Stockholders", "Net Income Including Noncontrolling Interests"])
        basic_eps = pick_first_valid_series(q_income, ["Basic EPS", "Diluted EPS"])
        diluted_eps = pick_first_valid_series(q_income, ["Diluted EPS", "Basic EPS"])
        cols = []
        for s in [revenue, operating_income, net_income, basic_eps, diluted_eps]:
            if s is not None:
                cols.extend(list(s.index))
        cols = sorted(set(cols), reverse=True)
        if not cols:
            return None
        revenue = revenue.reindex(cols) if revenue is not None else None
        operating_income = operating_income.reindex(cols) if operating_income is not None else None
        net_income = net_income.reindex(cols) if net_income is not None else None
        basic_eps = basic_eps.reindex(cols) if basic_eps is not None else None
        diluted_eps = diluted_eps.reindex(cols) if diluted_eps is not None else None
        eps_series = diluted_eps if diluted_eps is not None else basic_eps

        latest_revenue = revenue.iloc[0] if revenue is not None and len(revenue) >= 1 else None
        latest_net_income = net_income.iloc[0] if net_income is not None and len(net_income) >= 1 else None
        latest_operating_income = operating_income.iloc[0] if operating_income is not None and len(operating_income) >= 1 else None
        net_margin = None
        operating_margin = None
        if latest_revenue is not None and pd.notna(latest_revenue) and float(latest_revenue) != 0:
            if latest_net_income is not None and pd.notna(latest_net_income):
                net_margin = float(latest_net_income) / float(latest_revenue) * 100
            if latest_operating_income is not None and pd.notna(latest_operating_income):
                operating_margin = float(latest_operating_income) / float(latest_revenue) * 100

        eps_ttm = None
        latest_eps = None
        eps_growth_yoy = None
        if eps_series is not None and not eps_series.dropna().empty:
            eps_series = pd.to_numeric(eps_series, errors="coerce")
            latest_eps = eps_series.iloc[0] if len(eps_series) >= 1 and pd.notna(eps_series.iloc[0]) else None
            if len(eps_series.dropna()) >= 4:
                eps_ttm = eps_series.iloc[:4].sum()
            if len(eps_series) >= 5 and pd.notna(eps_series.iloc[0]) and pd.notna(eps_series.iloc[4]) and abs(float(eps_series.iloc[4])) > 1e-9:
                eps_growth_yoy = (float(eps_series.iloc[0]) - float(eps_series.iloc[4])) / abs(float(eps_series.iloc[4])) * 100

        info = getattr(ticker, "info", {}) or {}
        trailing_pe = info.get("trailingPE")
        forward_pe = info.get("forwardPE")
        pb = info.get("priceToBook")
        roe = info.get("returnOnEquity")
        if roe is not None:
            roe = float(roe) * 100

        return {
            "net_margin": round(net_margin, 2) if net_margin is not None else None,
            "operating_margin": round(operating_margin, 2) if operating_margin is not None else None,
            "eps_ttm": round(float(eps_ttm), 2) if eps_ttm is not None and pd.notna(eps_ttm) else None,
            "latest_eps": round(float(latest_eps), 2) if latest_eps is not None and pd.notna(latest_eps) else None,
            "eps_growth_yoy": round(float(eps_growth_yoy), 2) if eps_growth_yoy is not None and pd.notna(eps_growth_yoy) else None,
            "trailing_pe": safe_float(trailing_pe, 2),
            "forward_pe": safe_float(forward_pe, 2),
            "price_to_book": safe_float(pb, 2),
            "roe": safe_float(roe, 2),
            "source_note": "以 Yahoo Finance 財報 / info 資料估算。",
        }
    except Exception:
        return None


def common_metrics(hist: pd.DataFrame):
    hist = hist.copy()
    hist = hist[["Open", "High", "Low", "Close", "Volume"]].dropna()
    close = hist["Close"]
    volume = hist["Volume"]
    sma5 = close.rolling(5).mean()
    sma20 = close.rolling(20).mean()
    sma60 = close.rolling(60).mean()
    rsi14 = calc_rsi(close, 14)
    k, d = calc_kd(hist, 9, 3, 3)
    ret = close.pct_change()
    vol20 = ret.rolling(20).std() * math.sqrt(252) * 100
    vol_ma20 = volume.rolling(20).mean()
    bb_mid, bb_upper, bb_lower, bb_width = calc_bollinger(close, 20, 2)
    atr14 = calc_atr(hist, 14)
    sharpe_60 = (ret.rolling(60).mean() / ret.rolling(60).std()) * math.sqrt(252)
    return {
        "close": float(close.iloc[-1]),
        "prev_close": float(close.iloc[-2]) if len(close) >= 2 else None,
        "sma5": float(sma5.iloc[-1]) if not pd.isna(sma5.iloc[-1]) else None,
        "sma20": float(sma20.iloc[-1]) if not pd.isna(sma20.iloc[-1]) else None,
        "sma60": float(sma60.iloc[-1]) if not pd.isna(sma60.iloc[-1]) else None,
        "prev_sma20": float(sma20.iloc[-2]) if len(sma20) >= 2 and not pd.isna(sma20.iloc[-2]) else None,
        "prev_sma60": float(sma60.iloc[-2]) if len(sma60) >= 2 and not pd.isna(sma60.iloc[-2]) else None,
        "rsi14": float(rsi14.iloc[-1]) if not pd.isna(rsi14.iloc[-1]) else None,
        "k": float(k.iloc[-1]) if not pd.isna(k.iloc[-1]) else None,
        "d": float(d.iloc[-1]) if not pd.isna(d.iloc[-1]) else None,
        "prev_k": float(k.iloc[-2]) if len(k) >= 2 and not pd.isna(k.iloc[-2]) else None,
        "prev_d": float(d.iloc[-2]) if len(d) >= 2 and not pd.isna(d.iloc[-2]) else None,
        "vol20": float(vol20.iloc[-1]) if not pd.isna(vol20.iloc[-1]) else None,
        "last_volume": float(volume.iloc[-1]) if not pd.isna(volume.iloc[-1]) else None,
        "vol_ma20": float(vol_ma20.iloc[-1]) if not pd.isna(vol_ma20.iloc[-1]) else None,
        "support": float(close.tail(20).min()),
        "resistance": float(close.tail(20).max()),
        "bb_mid": float(bb_mid.iloc[-1]) if not pd.isna(bb_mid.iloc[-1]) else None,
        "bb_upper": float(bb_upper.iloc[-1]) if not pd.isna(bb_upper.iloc[-1]) else None,
        "bb_lower": float(bb_lower.iloc[-1]) if not pd.isna(bb_lower.iloc[-1]) else None,
        "bb_width": float(bb_width.iloc[-1]) if not pd.isna(bb_width.iloc[-1]) else None,
        "atr14": float(atr14.iloc[-1]) if not pd.isna(atr14.iloc[-1]) else None,
        "sharpe60": float(sharpe_60.iloc[-1]) if not pd.isna(sharpe_60.iloc[-1]) else None,
        "daily_ret_mean": float(ret.tail(60).mean()) if len(ret.dropna()) >= 20 else None,
        "close_series": close,
        "sma20_series": sma20,
        "sma60_series": sma60,
    }


def granville_signal(m: dict):
    close = m.get("close")
    prev_close = m.get("prev_close")
    sma20 = m.get("sma20")
    prev_sma20 = m.get("prev_sma20")
    if None in [close, prev_close, sma20, prev_sma20]:
        return {"rule": None, "signal": "資料不足", "score": 0, "reason": "葛蘭碧法則資料不足"}
    ma_up = sma20 > prev_sma20
    ma_down = sma20 < prev_sma20
    crossed_up = prev_close <= prev_sma20 and close > sma20
    crossed_down = prev_close >= prev_sma20 and close < sma20
    deviation_pct = ((close - sma20) / sma20) * 100 if sma20 != 0 else 0
    if ma_up and crossed_up:
        return {"rule": "B1", "signal": "偏多訊號", "score": 2, "reason": "均線往上，價格剛站回均線上方"}
    if ma_up and close < sma20 and deviation_pct <= -5:
        return {"rule": "B2", "signal": "回檔觀察", "score": 1, "reason": "均線往上，但價格拉回較多，留意止穩"}
    if ma_up and close > sma20 and 0 <= deviation_pct <= 3:
        return {"rule": "B3", "signal": "偏多延續", "score": 1, "reason": "均線往上，價格貼近均線上方整理"}
    if ma_down and deviation_pct <= -8:
        return {"rule": "B4", "signal": "跌深反彈留意", "score": 1, "reason": "價格離均線太遠，可能有技術反彈"}
    if ma_down and crossed_down:
        return {"rule": "S1", "signal": "偏弱訊號", "score": -2, "reason": "均線往下，價格剛跌破均線"}
    if ma_down and close > sma20 and deviation_pct >= 5:
        return {"rule": "S2", "signal": "反彈過大", "score": -1, "reason": "均線往下，價格反彈太多，追價風險高"}
    if ma_down and close < sma20 and -3 <= deviation_pct <= 0:
        return {"rule": "S3", "signal": "弱勢整理", "score": -1, "reason": "均線往下，價格靠近均線但仍偏弱"}
    if ma_up and deviation_pct >= 8:
        return {"rule": "S4", "signal": "漲多留意拉回", "score": -1, "reason": "價格離均線太遠，短線可能拉回"}
    return {"rule": "中性", "signal": "未出現明確訊號", "score": 0, "reason": "目前價格與均線關係沒有明顯買賣訊號"}


def estimate_ma_cross_time(hist: pd.DataFrame):
    try:
        close = hist["Close"].dropna()
        sma20 = close.rolling(20).mean()
        sma60 = close.rolling(60).mean()
        joined = pd.concat([close.rename("close"), sma20.rename("s20"), sma60.rename("s60")], axis=1).dropna()
        if len(joined) < 20:
            return None

        spread = joined["s20"] - joined["s60"]
        current = float(spread.iloc[-1])
        short_change = spread.diff().tail(5).mean()
        recent_change = spread.diff().tail(10).mean()
        weighted_change = None
        if not pd.isna(short_change) and not pd.isna(recent_change):
            weighted_change = float(short_change) * 0.6 + float(recent_change) * 0.4
        elif not pd.isna(short_change):
            weighted_change = float(short_change)
        elif not pd.isna(recent_change):
            weighted_change = float(recent_change)

        close_now = float(joined["close"].iloc[-1])
        close_prev = float(joined["close"].iloc[-2])
        sma20_now = float(joined["s20"].iloc[-1])
        sma20_prev = float(joined["s20"].iloc[-2])
        sma60_now = float(joined["s60"].iloc[-1])
        sma20_slope_series = joined["s20"].diff().tail(5)
        sma60_slope_series = joined["s60"].diff().tail(5)
        price_slope_series = joined["close"].diff().tail(5)
        sma20_slope = float(sma20_slope_series.mean()) if not pd.isna(sma20_slope_series.mean()) else 0.0
        sma60_slope = float(sma60_slope_series.mean()) if not pd.isna(sma60_slope_series.mean()) else 0.0
        price_slope = float(price_slope_series.mean()) if not pd.isna(price_slope_series.mean()) else 0.0
        granville_now = granville_signal_from_values(close_now, close_prev, sma20_now, sma20_prev) or {
            "rule": "中性", "signal": "未出現明確訊號", "reason": "目前價格與均線關係沒有明顯買賣訊號"
        }

        def build_cross_price(days_to_cross: int):
            projected_s20 = sma20_now + sma20_slope * days_to_cross
            projected_s60 = sma60_now + sma60_slope * days_to_cross
            projected_cross_ma = (projected_s20 + projected_s60) / 2
            projected_close = close_now + price_slope * days_to_cross
            return {
                "cross_price": round(float(projected_cross_ma), 2),
                "projected_close": round(float(projected_close), 2),
            }

        if weighted_change is None or abs(weighted_change) < 1e-9:
            return {
                "status": "暫無法估算",
                "days_to_cross": None,
                "cross_type": None,
                "estimated_date": None,
                "cross_price": None,
                "projected_close": None,
                "confidence": "低",
                "granville_basis": granville_now["rule"],
                "reason": f"均線差距變化太小，暫時無法依葛蘭碧節奏估算；目前屬 {granville_now['rule']}。",
            }

        base_days = abs(current / weighted_change)
        adjustment = 1.0
        next_cross = None

        if current < 0 and weighted_change > 0:
            next_cross = "黃金交叉"
            if granville_now["rule"] in {"B1", "B3"}:
                adjustment = 0.8
            elif granville_now["rule"] == "B2":
                adjustment = 0.9
            elif granville_now["rule"] in {"S1", "S3"}:
                adjustment = 1.25
            elif granville_now["rule"] in {"S2", "S4"}:
                adjustment = 1.4
        elif current > 0 and weighted_change < 0:
            next_cross = "死亡交叉"
            if granville_now["rule"] in {"S1", "S3"}:
                adjustment = 0.8
            elif granville_now["rule"] == "S2":
                adjustment = 0.9
            elif granville_now["rule"] in {"B1", "B3"}:
                adjustment = 1.25
            elif granville_now["rule"] in {"B2", "B4"}:
                adjustment = 1.4

        gap_ratio = abs(current) / max(abs(sma60_now), 1e-9) * 100
        confidence = "高" if gap_ratio <= 1.5 else ("中" if gap_ratio <= 3.5 else "低")

        if next_cross:
            days = int(max(1, round(base_days * adjustment)))
            est_date = (pd.Timestamp(joined.index[-1]) + pd.tseries.offsets.BDay(days)).strftime("%Y-%m-%d")
            cross_price_info = build_cross_price(days)
            return {
                "status": f"可能接近{next_cross}",
                "days_to_cross": days,
                "cross_type": next_cross,
                "estimated_date": est_date,
                "cross_price": cross_price_info["cross_price"],
                "projected_close": cross_price_info["projected_close"],
                "confidence": confidence,
                "granville_basis": granville_now["rule"],
                "reason": f"20MA 與 60MA 的差距正朝 {next_cross} 方向收斂，並依目前葛蘭碧 {granville_now['rule']}（{granville_now['signal']}）調整推估天數。",
            }

        trend = "20MA 持續在 60MA 上方" if current > 0 else "20MA 仍在 60MA 下方"
        return {
            "status": "目前未逼近交叉",
            "days_to_cross": None,
            "cross_type": None,
            "estimated_date": None,
            "cross_price": None,
            "projected_close": None,
            "confidence": confidence,
            "granville_basis": granville_now["rule"],
            "reason": f"{trend}；目前葛蘭碧判斷為 {granville_now['rule']}（{granville_now['signal']}），尚未形成明確交叉收斂。",
        }
    except Exception:
        return None

def infer_news_impact(news_items: list[dict], asset_type: str):
    positive_keywords = ["創新高", "成長", "上修", "合作", "擴產", "利多", "訂單", "獲利", "降息", "回購"]
    negative_keywords = ["下修", "衰退", "虧損", "利空", "關稅", "制裁", "戰爭", "通膨", "升息", "調查"]
    pos = neg = 0
    drivers = []
    for item in news_items or []:
        text = html.unescape((item.get("title") or "") + " " + (item.get("source") or ""))
        for kw in positive_keywords:
            if kw in text:
                pos += 1
                drivers.append(f"新聞含「{kw}」")
                break
        for kw in negative_keywords:
            if kw in text:
                neg += 1
                drivers.append(f"新聞含「{kw}」")
                break
    if pos == 0 and neg == 0:
        return {"view": "中性", "advice": "近期新聞沒有明顯偏多或偏空字眼，仍以技術面與基本面為主。", "drivers": ["未偵測到顯著事件關鍵字"]}
    if pos > neg:
        action = "可把新聞當加分項，但仍建議分批進場。" if asset_type in {"stock", "us_stock", "uk_stock"} else "可視為短線偏多題材，但不要只靠新聞追價。"
        return {"view": "事件面偏多", "advice": action, "drivers": drivers[:5]}
    if neg > pos:
        return {"view": "事件面偏空", "advice": "近期新聞偏向風險事件，建議拉高現金比重、避免重押，並用停損控管。", "drivers": drivers[:5]}
    return {"view": "事件面分歧", "advice": "近期消息多空交錯，建議用區間操作與分批策略。", "drivers": drivers[:5]}


def get_style_advice(asset_type: str, m: dict, scored: dict):
    vol20 = m.get("vol20") or 0
    score = scored.get("score") or 0
    rsi = m.get("rsi14")
    if asset_type in {"stock", "us_stock", "uk_stock"}:
        if score >= 5 and vol20 < 35:
            long_term = "較適合中長期分批持有，拉回靠近 20MA / 60MA 可留意加碼。"
        else:
            long_term = "較適合觀察後分批，不建議一次重押做長線。"
        if vol20 >= 35 and rsi is not None:
            day_trade = "波動偏大，若熟悉停損可做短線，但一定要嚴守紀律。"
        else:
            day_trade = "波動不算特別大，並不是最理想的當沖型標的。"
    else:
        long_term = "較適合波段 / 資產配置思維，不建議完全照股票長投方式看待。"
        day_trade = "若做短線，請以事件與波動風險為主，不宜過度擴大槓桿。"
    return {"long_term": long_term, "day_trade": day_trade}


def calc_target_price(m: dict):
    close = m.get("close")
    resistance = m.get("resistance")
    bb_upper = m.get("bb_upper")
    atr14 = m.get("atr14")
    if close is None:
        return None
    candidates = [x for x in [resistance, bb_upper, close + (atr14 or 0) * 1.5] if x is not None]
    if not candidates:
        return None
    conservative = min(candidates)
    aggressive = max(candidates)
    return {
        "conservative": round(float(conservative), 2),
        "aggressive": round(float(aggressive), 2),
        "basis": "以近20日壓力 / 布林上軌 / 1.5 倍 ATR 估算。",
    }


def score_signal(m: dict, asset_type: str, fundamentals: Optional[dict] = None):
    score = 0
    reasons = []
    risk_note = []
    granville = granville_signal(m)
    close = m.get("close")
    sma5 = m.get("sma5")
    sma20 = m.get("sma20")
    sma60 = m.get("sma60")
    rsi14 = m.get("rsi14")
    k = m.get("k")
    d = m.get("d")
    prev_k = m.get("prev_k")
    prev_d = m.get("prev_d")
    last_volume = m.get("last_volume")
    vol_ma20 = m.get("vol_ma20")
    support = m.get("support")
    resistance = m.get("resistance")
    bb_upper = m.get("bb_upper")
    bb_lower = m.get("bb_lower")

    if close is not None and sma20 is not None:
        if close > sma20:
            score += 1; reasons.append("價格在20MA之上")
        else:
            score -= 1; reasons.append("價格在20MA之下")
    if sma5 is not None and sma20 is not None:
        if sma5 > sma20:
            score += 1; reasons.append("短線均線在中期均線之上")
        else:
            score -= 1; reasons.append("短線均線仍在中期均線之下")
    if sma20 is not None and sma60 is not None:
        if sma20 > sma60:
            score += 1; reasons.append("20MA 高於 60MA")
        else:
            score -= 1; reasons.append("20MA 仍低於 60MA")
    if rsi14 is not None:
        if rsi14 < 30:
            score += 2; reasons.append("RSI偏低，接近超賣區")
        elif rsi14 > 70:
            score -= 2; reasons.append("RSI偏高，接近過熱區")
        elif 45 <= rsi14 <= 65:
            score += 1; reasons.append("RSI位置偏健康")
    if k is not None and d is not None:
        if k < 20 and d < 20:
            score += 1; reasons.append("KD在低檔區")
        elif k > 80 and d > 80:
            score -= 1; reasons.append("KD在高檔區")
    if prev_k is not None and prev_d is not None and k is not None and d is not None:
        if prev_k <= prev_d and k > d:
            score += 2; reasons.append("KD黃金交叉")
        elif prev_k >= prev_d and k < d:
            score -= 2; reasons.append("KD死亡交叉")
    if last_volume is not None and vol_ma20 is not None and vol_ma20 > 0:
        if last_volume > vol_ma20 * 1.2:
            score += 1; reasons.append("成交量比平常放大")
        elif last_volume < vol_ma20 * 0.8:
            score -= 1; reasons.append("成交量比平常偏小")
    if close is not None and bb_upper is not None and bb_lower is not None:
        if close > bb_upper:
            score -= 1; reasons.append("價格高於布林上軌，短線過熱")
        elif close < bb_lower:
            score += 1; reasons.append("價格接近或跌破布林下軌，留意反彈")
        else:
            reasons.append("價格位於布林通道內")

    score += granville["score"]
    reasons.append(f"葛蘭碧判斷：{granville['reason']}")

    if asset_type in {"stock", "us_stock", "uk_stock"}:
        if fundamentals:
            net_margin = fundamentals.get("net_margin")
            operating_margin = fundamentals.get("operating_margin")
            eps_ttm = fundamentals.get("eps_ttm")
            eps_growth_yoy = fundamentals.get("eps_growth_yoy")
            if net_margin is not None:
                score += 1 if net_margin >= 5 else -1
                reasons.append(f"單季稅後淨利率 {net_margin}%")
            if operating_margin is not None:
                score += 1 if operating_margin >= 10 else -1
                reasons.append(f"單季營業利益率 {operating_margin}%")
            if eps_ttm is not None:
                score += 1 if eps_ttm > 0 else -1
                reasons.append(f"近4季 EPS 合計 {eps_ttm}")
            if eps_growth_yoy is not None:
                if eps_growth_yoy >= 10:
                    score += 1
                elif eps_growth_yoy < 0:
                    score -= 1
                reasons.append(f"EPS 年增率 {eps_growth_yoy}%")
        else:
            reasons.append("基本面財報資料暫時抓不到")

    if close is not None and support is not None and close > 0:
        if (close - support) / close * 100 <= 3:
            risk_note.append("價格很接近近期支撐，若跌破要小心")
        else:
            risk_note.append("距離近期支撐還有一些緩衝")
    if close is not None and resistance is not None and close > 0 and (resistance - close) / close * 100 <= 3:
        risk_note.append("價格很接近近期壓力，不適合追高")
    if m.get("bb_width") is not None and m["bb_width"] > 20:
        risk_note.append("布林通道開口偏大，代表波動升高")

    if asset_type in {"stock", "us_stock", "uk_stock"}:
        if score >= 7:
            signal, action, timing, holder_action = "偏強", "可以開始小量分批買進，不要一次買滿。", "現在可以進場，但比較適合分批買。", "若已持有，可續抱；拉回不破支撐可考慮小幅加碼。"
        elif score >= 4:
            signal, action, timing, holder_action = "轉強中", "先放進觀察名單，也可以先小買一點。", "不是最漂亮的買點，等拉回或再確認會更安全。", "若已持有，可先續抱觀察。"
        elif score >= 0:
            signal, action, timing, holder_action = "方向不明", "先不要急著買。", "目前不是很明確的進場時機。", "若已持有可先續抱，但暫時不要加碼。"
        elif score >= -3:
            signal, action, timing, holder_action = "偏弱", "暫時不要新買，先保守。", "現在不是好的進場點。", "若已持有，先觀察支撐是否守住，跌破可考慮減碼。"
        else:
            signal, action, timing, holder_action = "明顯偏弱", "目前不建議進場。", "先等止跌或重新站回均線後再看。", "若已持有，優先檢查是否該停損或減碼。"
    elif asset_type == "index":
        if score >= 4:
            signal, action, timing, holder_action = "大盤轉強", "盤勢有轉強跡象，可開始留意機會。", "可觀察強勢股拉回是否出現買點。", "持股可續抱觀察。"
        elif score >= 0:
            signal, action, timing, holder_action = "大盤中性", "先觀察，不要太快重壓。", "目前不是很明確的大盤進場點。", "持股先續抱，但不急著加碼。"
        else:
            signal, action, timing, holder_action = "大盤偏弱", "宜保守，不建議積極進場。", "目前進場風險較高。", "持股留意支撐是否失守。"
    elif asset_type == "fx":
        if score >= 3:
            signal, action, timing, holder_action = "匯價轉強", "可以先小量換一部分。", "可先買一小部分，等拉回再補。", "已持有者可續抱。"
        elif score >= 0:
            signal, action, timing, holder_action = "匯價整理中", "先用定額或分批方式，不要急。", "目前不是最明確的換匯時點。", "已持有者續抱即可。"
        else:
            signal, action, timing, holder_action = "匯價偏弱", "先不要大額換匯。", "現在不是好的大額換匯點。", "若已持有，可先觀察。"
    else:
        if score >= 3:
            signal, action, timing, holder_action = "偏強", "可以分批布局。", "現在可開始慢慢買進。", "若已持有，可續抱。"
        elif score >= 0:
            signal, action, timing, holder_action = "整理中", "先不要急著重壓。", "目前不是很明確的進場點。", "已持有者先續抱。"
        else:
            signal, action, timing, holder_action = "偏弱", "先觀察，不急著買。", "等止穩後再考慮。", "若已持有，先保守看待。"
    return {"score": score, "signal": signal, "action": action, "timing": timing, "holder_action": holder_action, "reasons": reasons, "risk_note": risk_note, "granville_rule": granville["rule"], "granville_signal": granville["signal"], "granville_reason": granville["reason"]}


def analyze_dividend_yield(dividend_yield: Optional[float], estimated: bool = False):
    source_prefix = "系統自動估算" if estimated else "手動輸入"
    if dividend_yield is None:
        return {"is_high_yield": "未取得", "yield_level": "未判斷", "yield_advice": "目前無法取得近一年股利資料，因此無法判斷是否為高殖利率股。", "yield_source": "無資料"}
    if dividend_yield >= 8:
        return {"is_high_yield": "是", "yield_level": "高殖利率", "yield_advice": f"{source_prefix}殖利率偏高，可列入高殖利率股觀察，但要先確認是否為股價下跌造成的高殖利率。", "yield_source": source_prefix}
    if dividend_yield >= 6:
        return {"is_high_yield": "偏高", "yield_level": "中高殖利率", "yield_advice": f"{source_prefix}殖利率不錯，可搭配近年配息穩定性與配息率一起評估。", "yield_source": source_prefix}
    if dividend_yield >= 4:
        return {"is_high_yield": "普通", "yield_level": "一般殖利率", "yield_advice": f"{source_prefix}殖利率屬一般水準，適合和成長性、技術面一起綜合判斷。", "yield_source": source_prefix}
    return {"is_high_yield": "否", "yield_level": "低殖利率", "yield_advice": f"{source_prefix}殖利率偏低，較不屬於高殖利率股，若投資目標是現金流，可再比較其他標的。", "yield_source": source_prefix}


def analyze_cost_plan(current_price: float, cost: Optional[float], support: float, resistance: float, asset_type: str):
    if cost is None or current_price is None:
        return None
    pnl_pct = ((current_price - cost) / cost) * 100
    if asset_type in {"stock", "us_stock", "uk_stock"}:
        stop_loss_pct, take_profit_pct = -8, 15
    elif asset_type == "fx":
        stop_loss_pct, take_profit_pct = -3, 5
    elif asset_type == "commodity":
        stop_loss_pct, take_profit_pct = -6, 12
    elif asset_type == "index":
        stop_loss_pct, take_profit_pct = -5, 10
    else:
        stop_loss_pct, take_profit_pct = -5, 8
    if pnl_pct >= take_profit_pct:
        action = "已接近或達到停利區，可分批落袋。"
    elif pnl_pct >= 5:
        action = "已有一定獲利，可續抱，但可把停利點往上調。"
    elif pnl_pct > stop_loss_pct:
        action = "目前還在可接受範圍內，可續抱觀察。"
    else:
        action = "已接近或跌破停損區，建議重新檢查是否該減碼或停損。"
    support_note = f"可觀察 {round(support, 2)} 附近支撐是否守穩" if support is not None and current_price is not None and current_price >= support else (f"已跌破近20日支撐 {round(support, 2)}，風險升高" if support is not None and current_price is not None else "")
    resistance_note = f"上方可留意 {round(resistance, 2)} 附近壓力" if resistance is not None and current_price is not None else ""
    return {"cost": round(cost, 4), "pnl_pct": pnl_pct, "action": action, "support_note": support_note, "resistance_note": resistance_note, "stop_loss_pct": stop_loss_pct, "take_profit_pct": take_profit_pct}


def calc_order_plan(current_price: Optional[float], budget: Optional[float], asset_type: str, atr14: Optional[float], target_price: Optional[dict]):
    if current_price is None or budget is None or budget <= 0:
        return None
    if asset_type in {"stock", "us_stock", "uk_stock"}:
        risk_pct = 0.01
    elif asset_type in {"fx", "bond"}:
        risk_pct = 0.005
    else:
        risk_pct = 0.008
    stop_distance = atr14 if atr14 and atr14 > 0 else current_price * 0.05
    risk_amount = budget * risk_pct
    units_by_risk = max(1, int(risk_amount / stop_distance)) if stop_distance > 0 else 1
    units_by_cash = max(1, int(budget / current_price)) if current_price > 0 else 1
    suggested_units = min(units_by_risk, units_by_cash)
    suggested_amount = suggested_units * current_price
    stop_price = max(0, current_price - stop_distance)
    expected_profit = None
    rr_ratio = None
    if target_price and target_price.get("conservative"):
        expected_profit = (target_price["conservative"] - current_price) * suggested_units
        risk_total = (current_price - stop_price) * suggested_units
        if risk_total > 0:
            rr_ratio = expected_profit / risk_total
    return {
        "budget": round(float(budget), 2),
        "risk_pct": round(risk_pct * 100, 2),
        "suggested_units": suggested_units,
        "suggested_amount": round(float(suggested_amount), 2),
        "stop_price": round(float(stop_price), 2),
        "risk_amount": round(float(risk_amount), 2),
        "reward_risk_ratio": round(float(rr_ratio), 2) if rr_ratio is not None else None,
    }


def build_news_search_term(query: str, chinese_name: str, symbol: str, asset_type_label: str) -> str:
    base = (chinese_name or query or symbol).strip()
    suffix_map = {"股票": "股票 財經", "美股": "美股 財經", "英股": "英股 財經", "匯率": "匯率 財經", "債券": "債券 財經", "指數": "指數 財經", "原物料": "原物料 財經"}
    suffix = suffix_map.get(asset_type_label, "財經")
    return f"{base} {suffix}".strip()


def fetch_latest_chinese_news(query: str, limit: int = 5):
    if not query:
        return []
    url = f"https://news.google.com/rss/search?q={quote(query)}&hl=zh-TW&gl=TW&ceid=TW:zh-Hant"
    headers = {"User-Agent": "Mozilla/5.0", "Accept-Language": "zh-TW,zh;q=0.9,en;q=0.8"}
    try:
        req = Request(url, headers=headers)
        with urlopen(req, timeout=10) as resp:
            raw = resp.read()
        root = ET.fromstring(raw)
    except Exception:
        return []
    items, seen = [], set()
    for item in root.findall('.//item'):
        title = (item.findtext('title') or '').strip()
        link = (item.findtext('link') or '').strip()
        pub_date = (item.findtext('pubDate') or '').strip()
        source_node = item.find('source')
        source = (source_node.text or '').strip() if source_node is not None and source_node.text else 'Google 新聞'
        if not title or not link:
            continue
        key = (title, link)
        if key in seen:
            continue
        seen.add(key)
        items.append({"title": html.escape(title), "link": html.escape(link, quote=True), "source": html.escape(source), "pub_date": html.escape(pub_date)})
        if len(items) >= limit:
            break
    return items


def granville_signal_from_values(close_now, close_prev, sma20_now, sma20_prev):
    if None in [close_now, close_prev, sma20_now, sma20_prev]:
        return None
    if pd.isna(close_now) or pd.isna(close_prev) or pd.isna(sma20_now) or pd.isna(sma20_prev):
        return None
    ma_up = sma20_now > sma20_prev
    ma_down = sma20_now < sma20_prev
    crossed_up = close_prev <= sma20_prev and close_now > sma20_now
    crossed_down = close_prev >= sma20_prev and close_now < sma20_now
    deviation_pct = ((close_now - sma20_now) / sma20_now) * 100 if sma20_now != 0 else 0
    if ma_up and crossed_up:
        return {"rule": "B1", "side": "buy", "signal": "偏多訊號", "reason": "均線往上，價格剛站回均線上方"}
    if ma_up and close_now < sma20_now and deviation_pct <= -5:
        return {"rule": "B2", "side": "buy", "signal": "回檔觀察", "reason": "均線往上，但價格拉回較多，留意止穩"}
    if ma_up and close_now > sma20_now and 0 <= deviation_pct <= 3:
        return {"rule": "B3", "side": "buy", "signal": "偏多延續", "reason": "均線往上，價格貼近均線上方整理"}
    if ma_down and deviation_pct <= -8:
        return {"rule": "B4", "side": "buy", "signal": "跌深反彈留意", "reason": "價格離均線太遠，可能有技術反彈"}
    if ma_down and crossed_down:
        return {"rule": "S1", "side": "sell", "signal": "偏弱訊號", "reason": "均線往下，價格剛跌破均線"}
    if ma_down and close_now > sma20_now and deviation_pct >= 5:
        return {"rule": "S2", "side": "sell", "signal": "反彈過大", "reason": "均線往下，價格反彈太多，追價風險高"}
    if ma_down and close_now < sma20_now and -3 <= deviation_pct <= 0:
        return {"rule": "S3", "side": "sell", "signal": "弱勢整理", "reason": "均線往下，價格靠近均線但仍偏弱"}
    if ma_up and deviation_pct >= 8:
        return {"rule": "S4", "side": "sell", "signal": "漲多留意拉回", "reason": "價格離均線太遠，短線可能拉回"}
    return None


def detect_granville_points(hist: pd.DataFrame, lookback: int = 180):
    df = hist.copy().dropna().tail(max(lookback, 80))
    if df.empty or len(df) < 25:
        return []
    close = df["Close"]
    sma20 = close.rolling(20).mean()
    points = []
    for i in range(1, len(df)):
        signal = granville_signal_from_values(close.iloc[i], close.iloc[i - 1], sma20.iloc[i], sma20.iloc[i - 1])
        if not signal:
            continue
        point = dict(signal)
        point["date"] = df.index[i]
        point["price"] = float(close.iloc[i])
        points.append(point)
    return points


def create_chart_html(hist: pd.DataFrame, asset_type_label: str) -> str:
    df = hist.copy().dropna()
    if df.empty:
        return ""
    close = df["Close"]
    volume = df["Volume"]
    sma5 = close.rolling(5).mean()
    sma20 = close.rolling(20).mean()
    sma60 = close.rolling(60).mean()
    rsi14 = calc_rsi(close, 14)
    k, d = calc_kd(df, 9, 3, 3)
    bb_mid, bb_upper, bb_lower, _ = calc_bollinger(close, 20, 2)
    granville_points = detect_granville_points(df, lookback=180)

    fig = make_subplots(rows=4, cols=1, shared_xaxes=True, vertical_spacing=0.03, row_heights=[0.5, 0.15, 0.17, 0.18], subplot_titles=("K線圖（含布林通道 / 葛蘭碧買賣點）", "成交量", "RSI", "KD"))
    fig.add_trace(go.Candlestick(x=df.index, open=df["Open"], high=df["High"], low=df["Low"], close=df["Close"], name="K線"), row=1, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=sma5, mode="lines", name="5MA"), row=1, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=sma20, mode="lines", name="20MA"), row=1, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=sma60, mode="lines", name="60MA"), row=1, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=bb_upper, mode="lines", name="布林上軌", line=dict(dash="dot")), row=1, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=bb_mid, mode="lines", name="布林中軌", line=dict(dash="dot")), row=1, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=bb_lower, mode="lines", name="布林下軌", line=dict(dash="dot")), row=1, col=1)

    buy_points = [p for p in granville_points if p["side"] == "buy"]
    sell_points = [p for p in granville_points if p["side"] == "sell"]
    if buy_points:
        fig.add_trace(go.Scatter(x=[p["date"] for p in buy_points], y=[p["price"] for p in buy_points], mode="markers+text", name="葛蘭碧買點", text=[p["rule"] for p in buy_points], textposition="top center", marker=dict(symbol="triangle-up", size=12, color="#16a34a"), customdata=[[p["signal"], p["reason"]] for p in buy_points], hovertemplate="日期：%{x|%Y-%m-%d}<br>價位：%{y:.2f}<br>訊號：%{text}<br>狀態：%{customdata[0]}<br>說明：%{customdata[1]}<extra></extra>"), row=1, col=1)
    if sell_points:
        fig.add_trace(go.Scatter(x=[p["date"] for p in sell_points], y=[p["price"] for p in sell_points], mode="markers+text", name="葛蘭碧賣點", text=[p["rule"] for p in sell_points], textposition="bottom center", marker=dict(symbol="triangle-down", size=12, color="#dc2626"), customdata=[[p["signal"], p["reason"]] for p in sell_points], hovertemplate="日期：%{x|%Y-%m-%d}<br>價位：%{y:.2f}<br>訊號：%{text}<br>狀態：%{customdata[0]}<br>說明：%{customdata[1]}<extra></extra>"), row=1, col=1)
    fig.add_trace(go.Bar(x=df.index, y=volume, name="成交量"), row=2, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=rsi14, mode="lines", name="RSI"), row=3, col=1)
    fig.add_hline(y=70, row=3, col=1)
    fig.add_hline(y=30, row=3, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=k, mode="lines", name="K"), row=4, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=d, mode="lines", name="D"), row=4, col=1)
    fig.add_hline(y=80, row=4, col=1)
    fig.add_hline(y=20, row=4, col=1)
    fig.update_layout(height=980, xaxis_rangeslider_visible=False, margin=dict(l=20, r=20, t=50, b=20), legend=dict(orientation="h"), template="plotly_white", title=f"{asset_type_label} 技術圖表")
    return fig.to_html(full_html=False, include_plotlyjs="cdn")


def create_efficient_frontier_html(price_df: pd.DataFrame) -> str:
    if price_df is None or price_df.empty or price_df.shape[1] < 2:
        return ""
    returns = price_df.pct_change().dropna()
    if returns.empty:
        return ""
    mu = returns.mean() * 252
    cov = returns.cov() * 252
    assets = list(price_df.columns)
    points = []
    best_sharpe = None
    min_vol = None
    equal_weights = np.array([1 / len(assets)] * len(assets))
    np.random.seed(42)
    for _ in range(600):
        w = np.random.random(len(assets))
        w = w / w.sum()
        ret = float(np.dot(w, mu))
        vol = float(np.sqrt(np.dot(w.T, np.dot(cov, w))))
        sharpe = ret / vol if vol > 0 else None
        row = {"ret": ret, "vol": vol, "sharpe": sharpe, "weights": w}
        points.append(row)
        if sharpe is not None and (best_sharpe is None or sharpe > best_sharpe["sharpe"]):
            best_sharpe = row
        if min_vol is None or vol < min_vol["vol"]:
            min_vol = row
    eq_ret = float(np.dot(equal_weights, mu))
    eq_vol = float(np.sqrt(np.dot(equal_weights.T, np.dot(cov, equal_weights))))
    fig = go.Figure()
    fig.add_trace(go.Scatter(x=[p["vol"] * 100 for p in points], y=[p["ret"] * 100 for p in points], mode="markers", name="隨機組合", marker=dict(size=7, opacity=0.5)))
    if best_sharpe:
        fig.add_trace(go.Scatter(x=[best_sharpe["vol"] * 100], y=[best_sharpe["ret"] * 100], mode="markers+text", name="最大夏普", text=["最大夏普"], textposition="top center", marker=dict(size=14, color="#dc2626")))
    if min_vol:
        fig.add_trace(go.Scatter(x=[min_vol["vol"] * 100], y=[min_vol["ret"] * 100], mode="markers+text", name="最小波動", text=["最小波動"], textposition="bottom center", marker=dict(size=14, color="#2563eb")))
    fig.add_trace(go.Scatter(x=[eq_vol * 100], y=[eq_ret * 100], mode="markers+text", name="等權重", text=["等權重"], textposition="middle right", marker=dict(size=12, color="#16a34a")))
    fig.update_layout(title="效率前緣（年化報酬 / 年化波動）", template="plotly_white", xaxis_title="年化波動 %", yaxis_title="年化報酬 %", height=520, margin=dict(l=20, r=20, t=50, b=20))
    return fig.to_html(full_html=False, include_plotlyjs=False)


def compute_portfolio_analysis(symbols: list[str], market_scope: str = "auto"):
    cleaned = []
    for raw in symbols:
        s = raw.strip()
        if not s:
            continue
        sym = normalize_symbol(s, market_scope=market_scope if market_scope in {"us", "uk", "tw"} else "auto")
        cleaned.append(sym)
    cleaned = list(dict.fromkeys(cleaned))
    if len(cleaned) < 2:
        return None
    prices = pd.DataFrame()
    rows = []
    for sym in cleaned[:8]:
        hist, real = get_history(sym)
        if hist.empty or len(hist) < 70:
            continue
        close = hist["Close"].copy().rename(real)
        prices = pd.concat([prices, close], axis=1)
        ret = close.pct_change().dropna()
        if ret.empty:
            continue
        ann_ret = float(ret.mean() * 252)
        ann_vol = float(ret.std() * math.sqrt(252))
        sharpe = ann_ret / ann_vol if ann_vol > 0 else None
        rows.append({"symbol": real, "annual_return": ann_ret * 100, "annual_vol": ann_vol * 100, "sharpe": sharpe})
    prices = prices.dropna()
    if prices.shape[1] < 2 or not rows:
        return None
    rows = sorted(rows, key=lambda x: x["sharpe"] if x["sharpe"] is not None else -999, reverse=True)
    best = rows[0]
    frontier_html = create_efficient_frontier_html(prices)
    table_rows = "".join(f"<tr><td>{r['symbol']}</td><td>{round(r['annual_return'], 2)}%</td><td>{round(r['annual_vol'], 2)}%</td><td>{round(r['sharpe'], 2) if r['sharpe'] is not None else 'N/A'}</td></tr>" for r in rows)
    return {"rows": rows, "best": best, "frontier_html": frontier_html, "table_rows": table_rows}


def build_result_dict(title: str, asset_type: str, asset_type_label: str, query: str, symbol: str, hist: pd.DataFrame, m: dict, scored: dict, cost_info=None, dividend_yield: Optional[float] = None, dividend_estimated: bool = False, fundamentals: Optional[dict] = None, budget: Optional[float] = None):
    digits = 4 if asset_type_label == "匯率" else 2
    yield_info = analyze_dividend_yield(dividend_yield, estimated=dividend_estimated)
    chinese_name = get_chinese_name(query, symbol, asset_type)
    news_query = build_news_search_term(query, chinese_name, symbol, asset_type_label)
    latest_news = fetch_latest_chinese_news(news_query, limit=5)
    news_impact = infer_news_impact(latest_news, asset_type)
    ma_cross = estimate_ma_cross_time(hist)
    style_advice = get_style_advice(asset_type, m, scored)
    target_price = calc_target_price(m)
    order_plan = calc_order_plan(m.get("close"), budget, asset_type, m.get("atr14"), target_price)
    return {
        "title": f"{title}｜{query}", "asset_type": asset_type_label, "symbol": symbol, "chinese_name": chinese_name,
        "close": safe_float(m["close"], digits), "sma5": safe_float(m["sma5"], digits), "sma20": safe_float(m["sma20"], digits), "sma60": safe_float(m["sma60"], digits),
        "rsi14": safe_float(m["rsi14"], 1), "k": safe_float(m["k"], 1), "d": safe_float(m["d"], 1),
        "last_volume": safe_float(m["last_volume"], 0), "vol_ma20": safe_float(m["vol_ma20"], 0), "vol20": safe_float(m["vol20"], 1),
        "support": safe_float(m["support"], digits), "resistance": safe_float(m["resistance"], digits),
        "bb_upper": safe_float(m["bb_upper"], digits), "bb_mid": safe_float(m["bb_mid"], digits), "bb_lower": safe_float(m["bb_lower"], digits), "bb_width": safe_float(m["bb_width"], 2),
        "atr14": safe_float(m["atr14"], digits), "sharpe60": safe_float(m["sharpe60"], 2),
        "score": scored["score"], "signal": scored["signal"], "action": scored["action"], "timing": scored.get("timing"), "holder_action": scored.get("holder_action"),
        "reasons": scored["reasons"], "risk_note": scored["risk_note"], "granville_rule": scored.get("granville_rule"), "granville_signal": scored.get("granville_signal"), "granville_reason": scored.get("granville_reason"),
        "granville_points": detect_granville_points(hist, lookback=180), "cost_info": cost_info, "chart_html": create_chart_html(hist, asset_type_label),
        "dividend_yield": dividend_yield, "is_high_yield": yield_info["is_high_yield"], "yield_level": yield_info["yield_level"], "yield_advice": yield_info["yield_advice"], "yield_source": yield_info["yield_source"],
        "show_dividend_section": asset_type in {"stock", "us_stock", "uk_stock"}, "fundamentals": fundamentals, "news_query": news_query, "latest_news": latest_news,
        "news_impact": news_impact, "style_advice": style_advice, "target_price": target_price, "order_plan": order_plan, "ma_cross": ma_cross,
    }


def resolve_dividend_input_or_estimate(symbol: str, current_price: Optional[float], user_input_yield: Optional[float], asset_type: str):
    if asset_type not in {"stock", "us_stock", "uk_stock"}:
        return None, False
    if user_input_yield is not None:
        return user_input_yield, False
    estimated = estimate_dividend_yield(symbol, current_price)
    if estimated is not None:
        return estimated, True
    return None, False


def analyze_generic(symbol: str, query: str, title: str, asset_type: str, asset_label: str, cost: Optional[float], dividend_yield: Optional[float], budget: Optional[float]):
    hist, real_symbol = get_history(symbol)
    if hist.empty or len(hist) < 70:
        return None, f"找不到 {query} 的有效{asset_label}資料。"
    m = common_metrics(hist)
    fundamentals = get_fundamental_metrics(real_symbol, asset_type)
    scored = score_signal(m, asset_type, fundamentals)
    cost_info = analyze_cost_plan(m["close"], cost, m["support"], m["resistance"], asset_type)
    final_yield, estimated = resolve_dividend_input_or_estimate(real_symbol, m["close"], dividend_yield, asset_type)
    return build_result_dict(title, asset_type, asset_label, query, real_symbol, hist, m, scored, cost_info, final_yield, estimated, fundamentals, budget=budget), None


def analyze_target(query: str, market_scope: str = "auto", cost: Optional[float] = None, dividend_yield: Optional[float] = None, budget: Optional[float] = None):
    resolved_market = resolve_market_aware_symbol(query, market_scope=market_scope)
    if resolved_market.get("message"):
        return None, resolved_market["message"]
    symbol = resolved_market.get("symbol") or normalize_symbol(query, market_scope=market_scope)
    asset_type = detect_asset_type(query, symbol, market_scope=market_scope)
    if asset_type == "index":
        return analyze_generic(symbol, query, "指數技術分析", "index", "指數", cost, dividend_yield, budget)
    if asset_type == "fx":
        return analyze_generic(symbol, query, "匯率實戰策略", "fx", "匯率", cost, dividend_yield, budget)
    if asset_type == "bond":
        return analyze_generic(symbol, query, "債券實戰策略", "bond", "債券", cost, dividend_yield, budget)
    if asset_type == "commodity":
        return analyze_generic(symbol, query, "原物料技術分析", "commodity", "原物料", cost, dividend_yield, budget)
    if asset_type == "us_stock":
        return analyze_generic(symbol, query, "美股技術分析", "us_stock", "美股", cost, dividend_yield, budget)
    if asset_type == "uk_stock":
        return analyze_generic(symbol, query, "英股技術分析", "uk_stock", "英股", cost, dividend_yield, budget)
    resolved = resolve_tw_stock_symbol(query)
    if resolved:
        return analyze_generic(resolved["symbol"], query, "股票實戰策略", "stock", "股票", cost, dividend_yield, budget)
    resolved_uk = resolve_uk_stock_symbol(query)
    if resolved_uk:
        return analyze_generic(resolved_uk["symbol"], query, "英股技術分析", "uk_stock", "英股", cost, dividend_yield, budget)
    if query.strip().isdigit():
        return analyze_generic(symbol, query, "股票實戰策略", "stock", "股票", cost, dividend_yield, budget)
    tw_suggestions = suggest_tw_stock_names(query, limit=5)
    uk_suggestions = suggest_uk_stock_names(query, limit=5)
    if tw_suggestions or uk_suggestions:
        parts = []
        if tw_suggestions:
            parts.append("台股可能是：<br>" + "<br>".join(f"• {x}" for x in tw_suggestions))
        if uk_suggestions:
            pretty_uk = []
            seen = set()
            for x in uk_suggestions:
                symbol_guess = UK_NAME_MAP.get(x)
                label = f"{x}（{symbol_guess}）" if symbol_guess else x
                if label not in seen:
                    seen.add(label)
                    pretty_uk.append(label)
            parts.append("英股可能是：<br>" + "<br>".join(f"• {x}" for x in pretty_uk[:5]))
        return None, "找不到完全對應標的，你是不是想查：<br>" + "<br><br>".join(parts)
    return None, f"找不到「{query}」對應的股票、匯率、指數、原物料或債券資料。"


def format_analysis_html(result: dict, portfolio: Optional[dict] = None):
    score = result.get("score")
    score_class = "score-neutral"
    if score is not None:
        if score >= 6:
            score_class = "score-strong"
        elif score >= 3:
            score_class = "score-good"
        elif score < 0:
            score_class = "score-weak"
    reasons_html = "".join(f"<li>{r}</li>" for r in result.get("reasons", []))
    risks_html = "".join(f"<li>{r}</li>" for r in result.get("risk_note", []))

    dividend_block = ""
    if result.get("show_dividend_section"):
        dy = result.get("dividend_yield")
        dividend_block = f'''<div class="section"><h3>高殖利率股分析</h3><div class="grid"><div class="item"><span>殖利率</span><strong>{str(dy) + '%' if dy is not None else '未取得'}</strong></div><div class="item"><span>資料來源</span><strong>{result.get('yield_source')}</strong></div><div class="item"><span>高殖利率判斷</span><strong>{result.get('is_high_yield')}</strong></div><div class="item"><span>殖利率等級</span><strong>{result.get('yield_level')}</strong></div><div class="item wide"><span>高殖利率股建議</span><strong>{result.get('yield_advice')}</strong></div></div></div>'''

    fundamentals = result.get("fundamentals") or {}
    fundamental_block = ""
    if result.get("show_dividend_section"):
        fundamental_block = f"""
        <div class=\"section\"><h3>財報分析</h3><div class=\"grid\">
            <div class=\"item\"><span>單季稅後淨利率</span><strong>{str(fundamentals.get('net_margin')) + '%' if fundamentals.get('net_margin') is not None else '未取得'}</strong></div>
            <div class=\"item\"><span>單季營業利益率</span><strong>{str(fundamentals.get('operating_margin')) + '%' if fundamentals.get('operating_margin') is not None else '未取得'}</strong></div>
            <div class=\"item\"><span>近4季 EPS 合計</span><strong>{fundamentals.get('eps_ttm', '未取得')}</strong></div>
            <div class=\"item\"><span>最新單季 EPS</span><strong>{fundamentals.get('latest_eps', '未取得')}</strong></div>
            <div class=\"item\"><span>EPS 年增率</span><strong>{str(fundamentals.get('eps_growth_yoy')) + '%' if fundamentals.get('eps_growth_yoy') is not None else '未取得'}</strong></div>
            <div class=\"item\"><span>本益比(TTM)</span><strong>{fundamentals.get('trailing_pe', '未取得')}</strong></div>
            <div class=\"item\"><span>預估本益比</span><strong>{fundamentals.get('forward_pe', '未取得')}</strong></div>
            <div class=\"item\"><span>股價淨值比</span><strong>{fundamentals.get('price_to_book', '未取得')}</strong></div>
            <div class=\"item\"><span>ROE</span><strong>{str(fundamentals.get('roe')) + '%' if fundamentals.get('roe') is not None else '未取得'}</strong></div>
            <div class=\"item wide\"><span>資料說明</span><strong>{fundamentals.get('source_note', '無')}</strong></div>
        </div></div>
        """

    granville_points = result.get("granville_points", []) or []
    recent_points = list(reversed(granville_points[-5:]))
    if recent_points:
        recent_rows = "".join(f"<tr><td>{p['date'].strftime('%Y-%m-%d')}</td><td>{p['rule']}</td><td>{round(p['price'], 2)}</td><td>{p['signal']}</td><td>{p['reason']}</td></tr>" for p in recent_points)
        latest_point = recent_points[0]
        granville_recent_block = f"""<div class=\"section\"><h3>葛蘭碧買賣點標記</h3><div class=\"grid\"><div class=\"item\"><span>最近訊號日期</span><strong>{latest_point['date'].strftime('%Y-%m-%d')}</strong></div><div class=\"item\"><span>最近訊號代號</span><strong>{latest_point['rule']}</strong></div><div class=\"item\"><span>最近訊號價位</span><strong>{round(latest_point['price'], 2)}</strong></div><div class=\"item\"><span>最近訊號狀態</span><strong>{latest_point['signal']}</strong></div><div class=\"item wide\"><span>最近訊號說明</span><strong>{latest_point['reason']}</strong></div></div><div class=\"table-wrap\" style=\"margin-top:12px;\"><table class=\"score-table\"><thead><tr><th>日期</th><th>代號</th><th>價位</th><th>狀態</th><th>說明</th></tr></thead><tbody>{recent_rows}</tbody></table></div></div>"""
    else:
        granville_recent_block = "<div class='section'><h3>葛蘭碧買賣點標記</h3><ul><li>近 180 個交易日尚未偵測到明確的葛蘭碧買賣點。</li></ul></div>"

    ma_cross = result.get("ma_cross") or {}
    cross_block = f"""<div class=\"section\"><h3>黃金交叉 / 死亡交叉預估</h3><div class=\"grid\"><div class=\"item\"><span>目前狀態</span><strong>{ma_cross.get('status', '未取得')}</strong></div><div class=\"item\"><span>預估交叉類型</span><strong>{ma_cross.get('cross_type', '暫無')}</strong></div><div class=\"item\"><span>預估時間</span><strong>{str(ma_cross.get('days_to_cross')) + ' 個交易日' if ma_cross.get('days_to_cross') else '暫無法估算'}</strong></div><div class=\"item\"><span>預估日期</span><strong>{ma_cross.get('estimated_date', '暫無') or '暫無'}</strong></div><div class=\"item\"><span>交叉預定價格</span><strong>{ma_cross.get('cross_price', '暫無') if ma_cross.get('cross_price') is not None else '暫無'}</strong></div><div class=\"item\"><span>預估當日股價</span><strong>{ma_cross.get('projected_close', '暫無') if ma_cross.get('projected_close') is not None else '暫無'}</strong></div><div class=\"item\"><span>信心水準</span><strong>{ma_cross.get('confidence', '未取得')}</strong></div><div class=\"item\"><span>葛蘭碧依據</span><strong>{ma_cross.get('granville_basis', '未取得')}</strong></div><div class=\"item wide\"><span>說明</span><strong>{ma_cross.get('reason', '')}</strong></div></div></div>"""

    target_price = result.get("target_price") or {}
    target_block = f"""<div class=\"section\"><h3>上漲目標價</h3><div class=\"grid\"><div class=\"item\"><span>保守目標價</span><strong>{target_price.get('conservative', '未取得')}</strong></div><div class=\"item\"><span>積極目標價</span><strong>{target_price.get('aggressive', '未取得')}</strong></div><div class=\"item wide\"><span>估算依據</span><strong>{target_price.get('basis', '無')}</strong></div></div></div>"""

    style = result.get("style_advice") or {}
    style_block = f"""<div class=\"section\"><h3>操作風格建議</h3><div class=\"grid\"><div class=\"item wide\"><span>長期投資</span><strong>{style.get('long_term', '無')}</strong></div><div class=\"item wide\"><span>每日當沖 / 短線</span><strong>{style.get('day_trade', '無')}</strong></div></div></div>"""

    news_items = result.get("latest_news", []) or []
    if news_items:
        news_html = "".join(f'<li><a href="{n["link"]}" target="_blank" rel="noopener noreferrer">{n["title"]}</a><div class="news-meta">{n["source"]}｜{n["pub_date"]}</div></li>' for n in news_items)
    else:
        news_html = '<li>目前抓不到相關中文新聞，請稍後再試。</li>'
    news_impact = result.get("news_impact") or {}
    news_drivers = "".join(f"<li>{x}</li>" for x in news_impact.get("drivers", []))
    news_block = f'''<div class="section"><h3>最新五篇中文新聞</h3><div class="news-hint">搜尋關鍵字：{result.get('news_query')}</div><ul class="news-list">{news_html}</ul><div class="grid" style="margin-top:12px;"><div class="item"><span>事件面判斷</span><strong>{news_impact.get('view', '中性')}</strong></div><div class="item wide"><span>對投資策略可能影響</span><strong>{news_impact.get('advice', '無')}</strong></div></div><ul>{news_drivers if news_drivers else '<li>未抓到明顯事件字詞</li>'}</ul></div>'''

    order_block = ""
    order_plan = result.get("order_plan")
    if order_plan:
        order_block = f'''<div class="section"><h3>下單金額計算</h3><div class="grid"><div class="item"><span>投入預算</span><strong>{order_plan['budget']}</strong></div><div class="item"><span>單筆風險比例</span><strong>{order_plan['risk_pct']}%</strong></div><div class="item"><span>建議數量</span><strong>{order_plan['suggested_units']}</strong></div><div class="item"><span>建議下單金額</span><strong>{order_plan['suggested_amount']}</strong></div><div class="item"><span>參考停損價</span><strong>{order_plan['stop_price']}</strong></div><div class="item"><span>可承受風險金額</span><strong>{order_plan['risk_amount']}</strong></div><div class="item wide"><span>報酬風險比</span><strong>{order_plan['reward_risk_ratio'] if order_plan['reward_risk_ratio'] is not None else '未取得'}</strong></div></div></div>'''

    cost_block = ""
    cost_info = result.get("cost_info")
    if cost_info:
        cost_block = f'''<div class="section"><h3>成本價分析</h3><div class="grid"><div class="item"><span>持有成本</span><strong>{cost_info['cost']}</strong></div><div class="item"><span>目前損益</span><strong>{round(cost_info['pnl_pct'], 2)}%</strong></div><div class="item wide"><span>成本建議</span><strong>{cost_info['action']}</strong></div><div class="item wide"><span>支撐觀察</span><strong>{cost_info['support_note']}</strong></div><div class="item wide"><span>壓力觀察</span><strong>{cost_info['resistance_note']}</strong></div><div class="item"><span>參考停損</span><strong>{cost_info['stop_loss_pct']}%</strong></div><div class="item"><span>參考停利</span><strong>{cost_info['take_profit_pct']}%</strong></div></div></div>'''

    portfolio_block = ""
    if portfolio:
        portfolio_block = f'''<div class="section"><h3>效率前緣 / 夏普值排序</h3><div class="grid"><div class="item"><span>最大夏普標的</span><strong>{portfolio['best']['symbol']}</strong></div><div class="item"><span>最大夏普值</span><strong>{round(portfolio['best']['sharpe'], 2) if portfolio['best']['sharpe'] is not None else 'N/A'}</strong></div><div class="item"><span>年化報酬</span><strong>{round(portfolio['best']['annual_return'], 2)}%</strong></div><div class="item"><span>年化波動</span><strong>{round(portfolio['best']['annual_vol'], 2)}%</strong></div></div><div class="table-wrap" style="margin-top:12px;"><table class="score-table"><thead><tr><th>標的</th><th>年化報酬</th><th>年化波動</th><th>夏普值</th></tr></thead><tbody>{portfolio['table_rows']}</tbody></table></div><div class="section">{portfolio['frontier_html']}</div></div>'''

    return f'''
    <div class="result-card">
        <div class="result-head"><h2>{result.get('title', '查詢結果')}</h2><div class="score {score_class}">綜合分數：{score}</div></div>
        <div class="grid">
            <div class="item"><span>查詢代碼</span><strong>{result.get('symbol')}</strong></div>
            <div class="item"><span>標的中文名稱</span><strong>{result.get('chinese_name')}</strong></div>
            <div class="item"><span>資產類型</span><strong>{result.get('asset_type')}</strong></div>
            <div class="item"><span>現價</span><strong>{result.get('close')}</strong></div>
            <div class="item"><span>5MA</span><strong>{result.get('sma5')}</strong></div>
            <div class="item"><span>20MA</span><strong>{result.get('sma20')}</strong></div>
            <div class="item"><span>60MA</span><strong>{result.get('sma60')}</strong></div>
            <div class="item"><span>RSI</span><strong>{result.get('rsi14')}</strong></div>
            <div class="item"><span>K值</span><strong>{result.get('k')}</strong></div>
            <div class="item"><span>D值</span><strong>{result.get('d')}</strong></div>
            <div class="item"><span>成交量</span><strong>{result.get('last_volume')}</strong></div>
            <div class="item"><span>20日均量</span><strong>{result.get('vol_ma20')}</strong></div>
            <div class="item"><span>年化波動</span><strong>{result.get('vol20')}%</strong></div>
            <div class="item"><span>60日夏普值</span><strong>{result.get('sharpe60')}</strong></div>
            <div class="item"><span>布林上軌</span><strong>{result.get('bb_upper')}</strong></div>
            <div class="item"><span>布林中軌</span><strong>{result.get('bb_mid')}</strong></div>
            <div class="item"><span>布林下軌</span><strong>{result.get('bb_lower')}</strong></div>
            <div class="item"><span>布林寬度</span><strong>{result.get('bb_width')}%</strong></div>
            <div class="item"><span>ATR14</span><strong>{result.get('atr14')}</strong></div>
            <div class="item"><span>近20日支撐</span><strong>{result.get('support')}</strong></div>
            <div class="item"><span>近20日壓力</span><strong>{result.get('resistance')}</strong></div>
            <div class="item"><span>葛蘭碧法則</span><strong>{result.get('granville_rule')}</strong></div>
            <div class="item wide"><span>葛蘭碧判斷</span><strong>{result.get('granville_signal')}</strong></div>
            <div class="item wide"><span>現在狀態</span><strong>{result.get('signal')}</strong></div>
            <div class="item wide"><span>適合動作</span><strong>{result.get('action')}</strong></div>
            <div class="item wide"><span>進場時機</span><strong>{result.get('timing')}</strong></div>
            <div class="item wide"><span>持有者動作</span><strong>{result.get('holder_action')}</strong></div>
        </div>
        {fundamental_block}
        {dividend_block}
        {cross_block}
        {granville_recent_block}
        <div class="section"><h3>葛蘭碧八大法則</h3><ul><li>{result.get('granville_reason')}</li></ul></div>
        <div class="section"><h3>判斷依據</h3><ul>{reasons_html}</ul></div>
        <div class="section"><h3>風險提醒</h3><ul>{risks_html if risks_html else '<li>無</li>'}</ul></div>
        {style_block}
        {target_block}
        {order_block}
        {cost_block}
        {portfolio_block}
        {news_block}
        <div class="section"><h3>技術圖表</h3>{result.get('chart_html', '')}</div>
    </div>
    '''


HTML_TEMPLATE = """
<!doctype html>
<html lang="zh-Hant">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>投資查詢平台 v16.1</title>
    <style>
        body { margin: 0; font-family: "Microsoft JhengHei", Arial, sans-serif; background: #f5f7fb; color: #1f2937; }
        .container { max-width: 1300px; margin: 30px auto; padding: 20px; }
        .card { background: white; border-radius: 18px; padding: 24px; box-shadow: 0 8px 24px rgba(0,0,0,0.08); margin-bottom: 20px; }
        h1 { margin-top: 0; font-size: 30px; }
        .sub { color: #6b7280; margin-bottom: 18px; line-height: 1.8; }
        form { display: grid; grid-template-columns: 2fr 1fr 1fr 1fr 1fr auto; gap: 12px; }
        input, select { padding: 14px 16px; border-radius: 12px; border: 1px solid #d1d5db; font-size: 16px; }
        button { padding: 14px 20px; border: none; border-radius: 12px; background: #2563eb; color: white; font-size: 16px; cursor: pointer; }
        .tips { margin-top: 14px; color: #4b5563; line-height: 1.8; }
        .error { background: #fef2f2; color: #b91c1c; border: 1px solid #fecaca; border-radius: 12px; padding: 14px; margin-top: 16px; }
        .result-card { background: white; border-radius: 18px; padding: 24px; box-shadow: 0 8px 24px rgba(0,0,0,0.08); }
        .result-head { display: flex; justify-content: space-between; align-items: center; gap: 16px; flex-wrap: wrap; margin-bottom: 20px; }
        .result-head h2 { margin: 0; }
        .score { padding: 10px 14px; border-radius: 999px; font-weight: bold; }
        .score-strong { background: #dcfce7; color: #166534; }
        .score-good { background: #dbeafe; color: #1d4ed8; }
        .score-neutral { background: #f3f4f6; color: #374151; }
        .score-weak { background: #fee2e2; color: #991b1b; }
        .grid { display: grid; grid-template-columns: repeat(4, 1fr); gap: 12px; }
        .item { background: #f8fafc; border-radius: 12px; padding: 12px; border: 1px solid #e5e7eb; }
        .item span { display: block; color: #6b7280; font-size: 13px; margin-bottom: 6px; }
        .item strong { font-size: 18px; }
        .wide { grid-column: span 2; }
        .section { margin-top: 22px; }
        .section h3 { margin-bottom: 10px; }
        .table-wrap { overflow-x: auto; }
        .score-table { width: 100%; border-collapse: collapse; background: #fff; border-radius: 12px; overflow: hidden; border: 1px solid #e5e7eb; }
        .score-table th, .score-table td { padding: 12px; border-bottom: 1px solid #e5e7eb; text-align: left; font-size: 14px; }
        .score-table th { background: #eff6ff; color: #1e3a8a; }
        .score-table tr:last-child td { border-bottom: none; }
        ul { margin: 0; padding-left: 20px; line-height: 1.8; }
        .quick-links { margin-top: 12px; display: flex; flex-wrap: wrap; gap: 10px; }
        .quick-links a { display: inline-block; padding: 8px 12px; border-radius: 999px; background: #e0e7ff; color: #3730a3; text-decoration: none; font-size: 14px; }
        .news-meta, .news-hint { color: #6b7280; font-size: 13px; margin-top: 4px; }
        @media (max-width: 1100px) { form { grid-template-columns: 1fr 1fr 1fr; } }
        @media (max-width: 900px) { form { grid-template-columns: 1fr; } .grid { grid-template-columns: repeat(2, 1fr); } .wide { grid-column: span 2; } }
        @media (max-width: 560px) { .grid { grid-template-columns: 1fr; } .wide { grid-column: span 1; } }
    </style>
</head>
<body>
    <div class="container">
        <div class="card">
            <h1>投資查詢平台 v16.1</h1>
            <div class="sub">
                支援台股、美股、英股、台灣加權指數、匯率、原物料、債券 ETF。<br>
                新增市場選項避免英股 / 美股代號重複，並支援英股公司中文名、英文名與常見簡稱對照查詢；同時加入依葛蘭碧八大法則調整的黃金交叉 / 死亡交叉到達時間預估、布林通道、財報分析、EPS 與 EPS 成長率、時事影響判讀、長期 / 當沖建議、下單金額計算、上漲目標價，以及多標的效率前緣與夏普值排序。
            </div>
            <form method="post">
                <input type="text" name="query" placeholder="單一標的：台積電、AAPL、HSBA、匯豐、力拓、黃金、美債" value="{{ query or '' }}" required>
                <select name="market_scope">
                    <option value="auto" {% if market_scope == 'auto' %}selected{% endif %}>自動判斷市場</option>
                    <option value="tw" {% if market_scope == 'tw' %}selected{% endif %}>台股</option>
                    <option value="us" {% if market_scope == 'us' %}selected{% endif %}>美股</option>
                    <option value="uk" {% if market_scope == 'uk' %}selected{% endif %}>英股</option>
                </select>
                <input type="number" step="0.0001" name="cost" placeholder="成本價，可不填" value="{{ cost or '' }}">
                <input type="number" step="0.01" name="dividend_yield" placeholder="殖利率%，可不填" value="{{ dividend_yield or '' }}">
                <input type="number" step="0.01" name="budget" placeholder="預算，可不填" value="{{ budget or '' }}">
                <button type="submit">開始查詢</button>
                <input type="text" name="portfolio_symbols" placeholder="多標的效率前緣：AAPL,MSFT,NVDA" value="{{ portfolio_symbols or '' }}">
            </form>
            <div class="tips">
                範例 1：查 KEN、VOD、RIO 這類代號時，若系統偵測可能同時對應美股 / 英股，會要求你先指定市場，避免抓錯標的。<br>
                範例 2：英股可直接輸入公司名稱，例如：匯豐、HSBC、巴克萊、力拓、Shell。<br>
                範例 3：多標的效率前緣可輸入 AAPL,MSFT,NVDA,QQQ。<br>
                若填入預算，系統會估算建議下單金額、建議數量、停損價與報酬風險比。
            </div>
            <div class="quick-links">
                <a href="/?q=台積電">台積電</a>
                <a href="/?q=0050">0050</a>
                <a href="/?q=AAPL&market_scope=us">AAPL</a>
                <a href="/?q=HSBA&market_scope=uk">HSBA</a>
                <a href="/?q=%E5%8C%AF%E8%B1%90&market_scope=uk">匯豐</a>
                <a href="/?q=%E5%8A%9B%E6%8B%93&market_scope=uk">力拓</a>
                <a href="/?q=美元">美元</a>
                <a href="/?q=美債">美債</a>
                <a href="/?q=黃金">黃金</a>
            </div>
        </div>
        {% if error %}<div class="error">{{ error|safe }}</div>{% endif %}
        {% if result_html %}{{ result_html|safe }}{% endif %}
    </div>
</body>
</html>
"""


@app.route("/", methods=["GET", "POST"])
def index():
    result_html = None
    error = None
    query = ""
    cost = ""
    dividend_yield = ""
    budget = ""
    market_scope = "auto"
    portfolio_symbols = ""
    if request.method == "GET":
        query = (request.args.get("q") or "").strip()
        cost = (request.args.get("cost") or "").strip()
        dividend_yield = (request.args.get("dividend_yield") or "").strip()
        budget = (request.args.get("budget") or "").strip()
        market_scope = (request.args.get("market_scope") or "auto").strip()
        portfolio_symbols = (request.args.get("portfolio_symbols") or "").strip()
    else:
        query = (request.form.get("query") or "").strip()
        cost = (request.form.get("cost") or "").strip()
        dividend_yield = (request.form.get("dividend_yield") or "").strip()
        budget = (request.form.get("budget") or "").strip()
        market_scope = (request.form.get("market_scope") or "auto").strip()
        portfolio_symbols = (request.form.get("portfolio_symbols") or "").strip()

    parsed_cost = None
    parsed_dividend_yield = None
    parsed_budget = None
    if cost:
        try:
            parsed_cost = float(cost)
        except ValueError:
            error = "成本價格式錯誤，請輸入數字。"
    if dividend_yield and error is None:
        try:
            parsed_dividend_yield = float(dividend_yield)
        except ValueError:
            error = "殖利率格式錯誤，請輸入數字。"
    if budget and error is None:
        try:
            parsed_budget = float(budget)
        except ValueError:
            error = "預算格式錯誤，請輸入數字。"

    portfolio = None
    if portfolio_symbols:
        try:
            portfolio = compute_portfolio_analysis([x for x in portfolio_symbols.split(",") if x.strip()], market_scope=market_scope)
        except Exception:
            portfolio = None

    if query and error is None:
        result, err = analyze_target(query, market_scope=market_scope, cost=parsed_cost, dividend_yield=parsed_dividend_yield, budget=parsed_budget)
        if err:
            error = err
        else:
            result_html = format_analysis_html(result, portfolio=portfolio)
    elif portfolio and error is None:
        dummy = {
            "title": "投資組合分析", "score": 0, "symbol": "-", "chinese_name": "-", "asset_type": "組合", "close": "-", "sma5": "-", "sma20": "-", "sma60": "-",
            "rsi14": "-", "k": "-", "d": "-", "last_volume": "-", "vol_ma20": "-", "vol20": "-", "sharpe60": "-", "bb_upper": "-", "bb_mid": "-", "bb_lower": "-", "bb_width": "-",
            "atr14": "-", "support": "-", "resistance": "-", "granville_rule": "-", "granville_signal": "-", "signal": "請查看下方效率前緣", "action": "此區塊僅顯示投資組合分析", "timing": "-", "holder_action": "-",
            "fundamentals": {}, "show_dividend_section": False, "ma_cross": {"status": "-", "cross_type": "-", "days_to_cross": None, "estimated_date": "-", "cross_price": None, "projected_close": None, "confidence": "-", "granville_basis": "-", "reason": "-"}, "granville_points": [], "granville_reason": "-",
            "reasons": [], "risk_note": [], "style_advice": {"long_term": "-", "day_trade": "-"}, "target_price": {"conservative": "-", "aggressive": "-", "basis": "-"}, "latest_news": [], "news_query": "-", "news_impact": {"view": "-", "advice": "-", "drivers": []}, "chart_html": ""
        }
        result_html = format_analysis_html(dummy, portfolio=portfolio)

    return render_template_string(HTML_TEMPLATE, result_html=result_html, error=error, query=query, cost=cost, dividend_yield=dividend_yield, budget=budget, market_scope=market_scope, portfolio_symbols=portfolio_symbols)


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 10000))
    app.run(host="0.0.0.0", port=port, debug=False)
