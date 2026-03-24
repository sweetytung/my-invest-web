from flask import Flask, request, render_template_string
import math
import difflib
import os
from typing import Tuple, Optional

import pandas as pd
import yfinance as yf
import twstock
import plotly.graph_objects as go
from plotly.subplots import make_subplots

app = Flask(__name__)

# =========================================================
# 1) 關鍵字對照：匯率 / 債券 / 指數 / 原物料
# =========================================================
KEYWORD_MAP = {
    # 匯率
    "美元": "USDTWD=X",
    "美元兌台幣": "USDTWD=X",
    "usd/twd": "USDTWD=X",
    "澳幣": "AUDTWD=X",
    "澳幣兌台幣": "AUDTWD=X",
    "aud/twd": "AUDTWD=X",
    "日圓": "JPYTWD=X",
    "日幣": "JPYTWD=X",
    "jpy/twd": "JPYTWD=X",
    "歐元": "EURTWD=X",
    "eur/twd": "EURTWD=X",

    # 債券 / 債券 ETF
    "美債": "TLT",
    "20年美債": "TLT",
    "長天期美債": "TLT",
    "7-10年美債": "IEF",
    "中天期美債": "IEF",
    "短債": "SHY",
    "投等債": "LQD",
    "投資等級債": "LQD",
    "非投等債": "HYG",
    "高收益債": "HYG",
    "總體債券": "BND",
    "新興市場債": "EMB",

    # 指數
    "台灣加權指數": "^TWII",
    "台股加權指數": "^TWII",
    "台灣加權": "^TWII",
    "加權指數": "^TWII",
    "台股大盤": "^TWII",
    "大盤": "^TWII",
    "twii": "^TWII",
    "^twii": "^TWII",

    # 原物料 / 商品期貨
    "黃金": "GC=F",
    "金價": "GC=F",
    "gold": "GC=F",

    "白銀": "SI=F",
    "銀價": "SI=F",
    "silver": "SI=F",

    "白金": "PL=F",
    "platinum": "PL=F",

    "鈀金": "PA=F",
    "palladium": "PA=F",

    "原油": "CL=F",
    "紐約原油": "CL=F",
    "美國原油": "CL=F",
    "crude oil": "CL=F",
    "oil": "CL=F",

    "布蘭特原油": "BZ=F",
    "brent": "BZ=F",

    "天然氣": "NG=F",
    "natural gas": "NG=F",

    "銅": "HG=F",
    "copper": "HG=F",

    "玉米": "ZC=F",
    "corn": "ZC=F",

    "黃豆": "ZS=F",
    "大豆": "ZS=F",
    "soybean": "ZS=F",

    "小麥": "ZW=F",
    "wheat": "ZW=F",

    "咖啡": "KC=F",
    "coffee": "KC=F",

    "可可": "CC=F",
    "cocoa": "CC=F",

    "棉花": "CT=F",
    "cotton": "CT=F",
}

BOND_SYMBOLS = {"TLT", "IEF", "SHY", "LQD", "HYG", "BND", "EMB"}
INDEX_SYMBOLS = {"^TWII"}
COMMODITY_SYMBOLS = {
    "GC=F", "SI=F", "PL=F", "PA=F", "CL=F", "BZ=F", "NG=F", "HG=F",
    "ZC=F", "ZS=F", "ZW=F", "KC=F", "CC=F", "CT=F"
}

# =========================================================
# 2) 台股中文名稱索引
# =========================================================
TW_NAME_MAP = {}
TW_CODE_MAP = {}
TW_ALIAS_MAP = {}
TW_NAME_LIST = []


def normalize_name_text(text: str) -> str:
    if not text:
        return ""
    s = str(text).strip()
    s = s.replace(" ", "")
    s = s.replace("　", "")
    return s.upper()


def market_to_yf_suffix(market: str) -> str:
    if str(market).strip() == "上市":
        return ".TW"
    if str(market).strip() == "上櫃":
        return ".TWO"
    return ""


def build_twstock_maps() -> None:
    global TW_NAME_MAP, TW_CODE_MAP, TW_ALIAS_MAP, TW_NAME_LIST

    name_map = {}
    code_map = {}
    alias_map = {}

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

            if stock_name == "台塑":
                alias_map["台塑"] = yf_symbol

            if stock_name == "鴻海":
                alias_map["鴻海"] = yf_symbol

            if stock_name == "聯發科":
                alias_map["聯發科"] = yf_symbol

        except Exception:
            continue

    TW_NAME_MAP = name_map
    TW_CODE_MAP = code_map
    TW_ALIAS_MAP = alias_map
    TW_NAME_LIST = sorted(set(list(name_map.keys()) + list(alias_map.keys())))

    print("台股名稱索引載入完成")
    print("TW_NAME_MAP:", len(TW_NAME_MAP))
    print("TW_CODE_MAP:", len(TW_CODE_MAP))
    print("TW_ALIAS_MAP:", len(TW_ALIAS_MAP))


build_twstock_maps()

# =========================================================
# 3) 共用工具
# =========================================================
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


def normalize_symbol(query: str) -> str:
    q = query.strip()
    q_lower = q.lower()

    if q_lower in KEYWORD_MAP:
        return KEYWORD_MAP[q_lower]
    if q in KEYWORD_MAP:
        return KEYWORD_MAP[q]

    q_upper = q.upper()
    if q_upper.endswith(".TW") or q_upper.endswith(".TWO") or q_upper.endswith("=X") or q_upper.startswith("^"):
        return q_upper

    resolved = resolve_tw_stock_symbol(q)
    if resolved:
        return resolved["symbol"]

    if q.isdigit():
        return f"{q}.TW"

    return q_upper


def detect_asset_type(query: str, symbol: str) -> str:
    q = query.strip().lower()

    if symbol in INDEX_SYMBOLS or any(x in q for x in ["加權指數", "台股大盤", "大盤", "台灣加權"]):
        return "index"

    if symbol.endswith("=X") or any(x in q for x in ["美元", "澳幣", "日圓", "日幣", "歐元"]):
        return "fx"

    if symbol in COMMODITY_SYMBOLS:
        return "commodity"

    commodity_keywords = [
        "黃金", "白銀", "原油", "天然氣", "銅", "玉米", "黃豆", "大豆",
        "小麥", "咖啡", "可可", "棉花", "白金", "鈀金"
    ]
    if any(k in query for k in commodity_keywords):
        return "commodity"

    bond_keywords = ["美債", "投等債", "投資等級債", "非投等債", "高收益債", "新興市場債", "債"]
    if any(k in query for k in bond_keywords):
        return "bond"

    if symbol in BOND_SYMBOLS:
        return "bond"

    return "stock"


def get_history(symbol: str) -> Tuple[pd.DataFrame, str]:
    ticker = yf.Ticker(symbol)
    hist = ticker.history(period="6mo", interval="1d", auto_adjust=False)

    if (hist.empty or len(hist) < 70) and symbol.endswith(".TW"):
        alt = symbol.replace(".TW", ".TWO")
        ticker = yf.Ticker(alt)
        hist_alt = ticker.history(period="6mo", interval="1d", auto_adjust=False)
        if not hist_alt.empty and len(hist_alt) >= 70:
            return hist_alt, alt

    return hist, symbol

# =========================================================
# 4) 指標 / 葛蘭碧
# =========================================================
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

    return {
        "close": float(close.iloc[-1]),
        "prev_close": float(close.iloc[-2]) if len(close) >= 2 else None,
        "sma5": float(sma5.iloc[-1]) if not pd.isna(sma5.iloc[-1]) else None,
        "sma20": float(sma20.iloc[-1]) if not pd.isna(sma20.iloc[-1]) else None,
        "sma60": float(sma60.iloc[-1]) if not pd.isna(sma60.iloc[-1]) else None,
        "prev_sma5": float(sma5.iloc[-2]) if len(sma5) >= 2 and not pd.isna(sma5.iloc[-2]) else None,
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
    }


def granville_signal(m: dict):
    close = m.get("close")
    prev_close = m.get("prev_close")
    sma20 = m.get("sma20")
    prev_sma20 = m.get("prev_sma20")

    if None in [close, prev_close, sma20, prev_sma20]:
        return {
            "rule": None,
            "signal": "資料不足",
            "score": 0,
            "reason": "葛蘭碧法則資料不足"
        }

    ma_up = sma20 > prev_sma20
    ma_down = sma20 < prev_sma20
    crossed_up = prev_close <= prev_sma20 and close > sma20
    crossed_down = prev_close >= prev_sma20 and close < sma20
    deviation_pct = ((close - sma20) / sma20) * 100 if sma20 != 0 else 0

    if ma_up and crossed_up:
        return {"rule": "買1", "signal": "偏多訊號", "score": 2, "reason": "均線往上，價格剛站回均線上方"}
    if ma_up and close < sma20 and deviation_pct <= -5:
        return {"rule": "買2", "signal": "回檔觀察", "score": 1, "reason": "均線往上，但價格拉回較多，留意止穩"}
    if ma_up and close > sma20 and 0 <= deviation_pct <= 3:
        return {"rule": "買3", "signal": "偏多延續", "score": 1, "reason": "均線往上，價格貼近均線上方整理"}
    if ma_down and deviation_pct <= -8:
        return {"rule": "買4", "signal": "跌深反彈留意", "score": 1, "reason": "價格離均線太遠，可能有技術反彈"}

    if ma_down and crossed_down:
        return {"rule": "賣1", "signal": "偏弱訊號", "score": -2, "reason": "均線往下，價格剛跌破均線"}
    if ma_down and close > sma20 and deviation_pct >= 5:
        return {"rule": "賣2", "signal": "反彈過大", "score": -1, "reason": "均線往下，價格反彈太多，追價風險高"}
    if ma_down and close < sma20 and -3 <= deviation_pct <= 0:
        return {"rule": "賣3", "signal": "弱勢整理", "score": -1, "reason": "均線往下，價格靠近均線但仍偏弱"}
    if ma_up and deviation_pct >= 8:
        return {"rule": "賣4", "signal": "漲多留意拉回", "score": -1, "reason": "價格離均線太遠，短線可能拉回"}

    return {
        "rule": "中性",
        "signal": "未出現明確訊號",
        "score": 0,
        "reason": "目前價格與均線關係沒有明顯買賣訊號"
    }


def score_signal(m: dict, asset_type: str):
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

    if close is not None and sma20 is not None:
        if close > sma20:
            score += 1
            reasons.append("價格在20MA之上")
        else:
            score -= 1
            reasons.append("價格在20MA之下")

    if sma5 is not None and sma20 is not None:
        if sma5 > sma20:
            score += 1
            reasons.append("短線均線在中期均線之上")
        else:
            score -= 1
            reasons.append("短線均線仍在中期均線之下")

    if sma20 is not None and sma60 is not None:
        if sma20 > sma60:
            score += 1
            reasons.append("中期趨勢比長期趨勢強")
        else:
            score -= 1
            reasons.append("中期趨勢仍弱於長期趨勢")

    if rsi14 is not None:
        if rsi14 < 30:
            score += 2
            reasons.append("RSI偏低，接近超賣區")
        elif rsi14 > 70:
            score -= 2
            reasons.append("RSI偏高，接近過熱區")
        elif 45 <= rsi14 <= 65:
            score += 1
            reasons.append("RSI位置偏健康")
        else:
            reasons.append("RSI沒有特別強弱")

    if k is not None and d is not None:
        if k < 20 and d < 20:
            score += 1
            reasons.append("KD在低檔區")
        elif k > 80 and d > 80:
            score -= 1
            reasons.append("KD在高檔區")
        else:
            reasons.append("KD不在極端區")

    if prev_k is not None and prev_d is not None and k is not None and d is not None:
        if prev_k <= prev_d and k > d:
            score += 2
            reasons.append("KD黃金交叉")
        elif prev_k >= prev_d and k < d:
            score -= 2
            reasons.append("KD死亡交叉")
        else:
            reasons.append("KD沒有明顯交叉")

    if last_volume is not None and vol_ma20 is not None and vol_ma20 > 0:
        if last_volume > vol_ma20 * 1.2:
            score += 1
            reasons.append("成交量比平常放大")
        elif last_volume < vol_ma20 * 0.8:
            score -= 1
            reasons.append("成交量比平常偏小")
        else:
            reasons.append("成交量大致正常")

    score += granville["score"]
    reasons.append(f"葛蘭碧判斷：{granville['reason']}")

    if close is not None and support is not None and close > 0:
        if (close - support) / close * 100 <= 3:
            risk_note.append("價格很接近近期支撐，若跌破要小心")
        else:
            risk_note.append("距離近期支撐還有一些緩衝")

    if close is not None and resistance is not None and close > 0:
        if (resistance - close) / close * 100 <= 3:
            risk_note.append("價格很接近近期壓力，不適合追高")

    # 白話版輸出
    if asset_type == "stock":
        if score >= 7:
            signal = "偏強"
            action = "可以開始小量分批買進，不要一次買滿。"
            timing = "現在可以進場，但比較適合分批買。"
            holder_action = "若已持有，可續抱；拉回不破支撐可考慮小幅加碼。"
        elif score >= 4:
            signal = "轉強中"
            action = "先放進觀察名單，也可以先小買一點。"
            timing = "不是最漂亮的買點，等拉回或再確認會更安全。"
            holder_action = "若已持有，可先續抱觀察。"
        elif score >= 0:
            signal = "方向不明"
            action = "先不要急著買。"
            timing = "目前不是很明確的進場時機。"
            holder_action = "若已持有可先續抱，但暫時不要加碼。"
        elif score >= -3:
            signal = "偏弱"
            action = "暫時不要新買，先保守。"
            timing = "現在不是好的進場點。"
            holder_action = "若已持有，先觀察支撐是否守住，跌破可考慮減碼。"
        else:
            signal = "明顯偏弱"
            action = "目前不建議進場。"
            timing = "先等止跌或重新站回均線後再看。"
            holder_action = "若已持有，優先檢查是否該停損或減碼。"

    elif asset_type == "index":
        if score >= 7:
            signal = "大盤偏強"
            action = "整體盤勢偏多，可偏多看待。"
            timing = "可以找強勢股分批布局，但不要追高。"
            holder_action = "持股可續抱。"
        elif score >= 4:
            signal = "大盤轉強"
            action = "盤勢有轉強跡象，可開始留意機會。"
            timing = "可觀察強勢股拉回是否出現買點。"
            holder_action = "持股可續抱觀察。"
        elif score >= 0:
            signal = "大盤中性"
            action = "先觀察，不要太快重壓。"
            timing = "目前不是很明確的大盤進場點。"
            holder_action = "持股先續抱，但不急著加碼。"
        elif score >= -3:
            signal = "大盤偏弱"
            action = "宜保守，不建議積極進場。"
            timing = "目前進場風險較高。"
            holder_action = "持股留意支撐是否失守。"
        else:
            signal = "大盤明顯偏弱"
            action = "先不要進場。"
            timing = "等盤勢止穩後再考慮。"
            holder_action = "持股宜保守，必要時降低部位。"

    elif asset_type == "fx":
        if score >= 6:
            signal = "匯價偏強"
            action = "可以分批換匯，但不要一次買滿。"
            timing = "現在可小量換匯，適合分批進。"
            holder_action = "若已持有外幣，可續抱觀察。"
        elif score >= 3:
            signal = "匯價轉強"
            action = "可以先小量換一部分。"
            timing = "可先買一小部分，等拉回再補。"
            holder_action = "已持有者可續抱。"
        elif score >= 0:
            signal = "匯價整理中"
            action = "先用定額或分批方式，不要急。"
            timing = "目前不是最明確的換匯時點。"
            holder_action = "已持有者續抱即可。"
        elif score >= -3:
            signal = "匯價偏弱"
            action = "先不要大額換匯。"
            timing = "現在不是好的大額換匯點。"
            holder_action = "若已持有，可先觀察。"
        else:
            signal = "匯價弱勢"
            action = "先等更低或更穩的點再換。"
            timing = "目前不建議積極換匯。"
            holder_action = "已持有者先保守看待。"

    elif asset_type == "commodity":
        if score >= 6:
            signal = "原物料偏強"
            action = "可以開始分批布局，但不要一次重押。"
            timing = "現在可小量進場，分批比較安全。"
            holder_action = "若已持有，可續抱觀察。"
        elif score >= 3:
            signal = "原物料轉強"
            action = "可先觀察，也可小量試單。"
            timing = "不是最漂亮的進場點，等拉回會更穩。"
            holder_action = "已持有者可續抱。"
        elif score >= 0:
            signal = "原物料整理中"
            action = "先觀察，不要急著買。"
            timing = "目前不是很明確的進場點。"
            holder_action = "若已持有可續抱，但先不要加碼。"
        elif score >= -3:
            signal = "原物料偏弱"
            action = "先不要新買。"
            timing = "現在不是好的進場時點。"
            holder_action = "若已持有，先觀察支撐。"
        else:
            signal = "原物料弱勢"
            action = "目前不建議進場。"
            timing = "先等止跌後再看。"
            holder_action = "若已持有，優先檢查是否該減碼。"

    else:  # bond
        if score >= 6:
            signal = "債券偏強"
            action = "可以分批配置。"
            timing = "現在可開始慢慢買進。"
            holder_action = "若已持有，可續抱。"
        elif score >= 3:
            signal = "債券轉強"
            action = "可以先小量布局。"
            timing = "可先買一部分，等更好價格再補。"
            holder_action = "若已持有，可續抱觀察。"
        elif score >= 0:
            signal = "債券整理中"
            action = "先不要急著重壓。"
            timing = "目前不是很明確的進場點。"
            holder_action = "已持有者先續抱。"
        elif score >= -3:
            signal = "債券偏弱"
            action = "保守配置即可。"
            timing = "現在不適合積極加碼。"
            holder_action = "若已持有，留意是否跌破支撐。"
        else:
            signal = "債券弱勢"
            action = "先觀察，不急著買。"
            timing = "等止穩後再考慮。"
            holder_action = "若已持有，先保守看待。"

    return {
        "score": score,
        "signal": signal,
        "action": action,
        "timing": timing,
        "holder_action": holder_action,
        "reasons": reasons,
        "risk_note": risk_note,
        "granville_rule": granville["rule"],
        "granville_signal": granville["signal"],
        "granville_reason": granville["reason"],
    }

# =========================================================
# 5) 成本分析
# =========================================================
def analyze_cost_plan(current_price: float, cost: Optional[float], support: float, resistance: float, asset_type: str):
    if cost is None or current_price is None:
        return None

    pnl_pct = ((current_price - cost) / cost) * 100

    if asset_type == "stock":
        stop_loss_pct = -8
        take_profit_pct = 15
    elif asset_type == "fx":
        stop_loss_pct = -3
        take_profit_pct = 5
    elif asset_type == "commodity":
        stop_loss_pct = -6
        take_profit_pct = 12
    elif asset_type == "index":
        stop_loss_pct = -5
        take_profit_pct = 10
    else:
        stop_loss_pct = -5
        take_profit_pct = 8

    if pnl_pct >= take_profit_pct:
        action = "已接近或達到停利區，可分批落袋。"
    elif pnl_pct >= 5:
        action = "已有一定獲利，可續抱，但可把停利點往上調。"
    elif pnl_pct > stop_loss_pct:
        action = "目前還在可接受範圍內，可續抱觀察。"
    else:
        action = "已接近或跌破停損區，建議重新檢查是否該減碼或停損。"

    support_note = ""
    if support is not None and current_price is not None:
        if current_price >= support:
            support_note = f"可觀察 {round(support, 2)} 附近支撐是否守穩"
        else:
            support_note = f"已跌破近20日支撐 {round(support, 2)}，風險升高"

    resistance_note = ""
    if resistance is not None and current_price is not None:
        resistance_note = f"上方可留意 {round(resistance, 2)} 附近壓力"

    return {
        "cost": round(cost, 4),
        "pnl_pct": pnl_pct,
        "action": action,
        "support_note": support_note,
        "resistance_note": resistance_note,
        "stop_loss_pct": stop_loss_pct,
        "take_profit_pct": take_profit_pct,
    }

# =========================================================
# 6) 圖表
# =========================================================
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

    fig = make_subplots(
        rows=4,
        cols=1,
        shared_xaxes=True,
        vertical_spacing=0.03,
        row_heights=[0.5, 0.15, 0.17, 0.18],
        subplot_titles=("K線圖", "成交量", "RSI", "KD"),
    )

    fig.add_trace(
        go.Candlestick(
            x=df.index,
            open=df["Open"],
            high=df["High"],
            low=df["Low"],
            close=df["Close"],
            name="K線",
        ),
        row=1,
        col=1,
    )

    fig.add_trace(go.Scatter(x=df.index, y=sma5, mode="lines", name="5MA"), row=1, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=sma20, mode="lines", name="20MA"), row=1, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=sma60, mode="lines", name="60MA"), row=1, col=1)
    fig.add_trace(go.Bar(x=df.index, y=volume, name="成交量"), row=2, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=rsi14, mode="lines", name="RSI"), row=3, col=1)
    fig.add_hline(y=70, row=3, col=1)
    fig.add_hline(y=30, row=3, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=k, mode="lines", name="K"), row=4, col=1)
    fig.add_trace(go.Scatter(x=df.index, y=d, mode="lines", name="D"), row=4, col=1)
    fig.add_hline(y=80, row=4, col=1)
    fig.add_hline(y=20, row=4, col=1)

    fig.update_layout(
        height=950,
        xaxis_rangeslider_visible=False,
        margin=dict(l=20, r=20, t=50, b=20),
        legend=dict(orientation="h"),
        template="plotly_white",
        title=f"{asset_type_label} 技術圖表",
    )

    return fig.to_html(full_html=False, include_plotlyjs="cdn")

# =========================================================
# 7) 結果整理
# =========================================================
def build_result_dict(title: str, asset_type_label: str, query: str, symbol: str, hist: pd.DataFrame, m: dict, scored: dict, cost_info=None):
    digits = 4 if asset_type_label == "匯率" else 2
    return {
        "title": f"{title}｜{query}",
        "asset_type": asset_type_label,
        "symbol": symbol,
        "close": safe_float(m["close"], digits),
        "sma5": safe_float(m["sma5"], digits),
        "sma20": safe_float(m["sma20"], digits),
        "sma60": safe_float(m["sma60"], digits),
        "rsi14": safe_float(m["rsi14"], 1),
        "k": safe_float(m["k"], 1),
        "d": safe_float(m["d"], 1),
        "last_volume": safe_float(m["last_volume"], 0),
        "vol_ma20": safe_float(m["vol_ma20"], 0),
        "vol20": safe_float(m["vol20"], 1),
        "support": safe_float(m["support"], digits),
        "resistance": safe_float(m["resistance"], digits),
        "score": scored["score"],
        "signal": scored["signal"],
        "action": scored["action"],
        "timing": scored.get("timing"),
        "holder_action": scored.get("holder_action"),
        "reasons": scored["reasons"],
        "risk_note": scored["risk_note"],
        "granville_rule": scored.get("granville_rule"),
        "granville_signal": scored.get("granville_signal"),
        "granville_reason": scored.get("granville_reason"),
        "cost_info": cost_info,
        "chart_html": create_chart_html(hist, asset_type_label),
    }


def analyze_stock(symbol: str, query: str, cost: Optional[float] = None):
    hist, real_symbol = get_history(symbol)
    if hist.empty or len(hist) < 70:
        return None, f"找不到 {query} 的有效股票資料，請確認名稱或代碼是否正確。"
    m = common_metrics(hist)
    scored = score_signal(m, "stock")
    cost_info = analyze_cost_plan(m["close"], cost, m["support"], m["resistance"], "stock")
    return build_result_dict("股票實戰策略", "股票", query, real_symbol, hist, m, scored, cost_info), None


def analyze_fx(symbol: str, query: str, cost: Optional[float] = None):
    hist, real_symbol = get_history(symbol)
    if hist.empty or len(hist) < 70:
        return None, f"找不到 {query} 的有效匯率資料。"
    m = common_metrics(hist)
    scored = score_signal(m, "fx")
    cost_info = analyze_cost_plan(m["close"], cost, m["support"], m["resistance"], "fx")
    return build_result_dict("匯率實戰策略", "匯率", query, real_symbol, hist, m, scored, cost_info), None


def analyze_bond(symbol: str, query: str, cost: Optional[float] = None):
    hist, real_symbol = get_history(symbol)
    if hist.empty or len(hist) < 70:
        return None, f"找不到 {query} 的有效債券資料。"
    m = common_metrics(hist)
    scored = score_signal(m, "bond")
    cost_info = analyze_cost_plan(m["close"], cost, m["support"], m["resistance"], "bond")
    return build_result_dict("債券實戰策略", "債券", query, real_symbol, hist, m, scored, cost_info), None


def analyze_index(symbol: str, query: str, cost: Optional[float] = None):
    hist, real_symbol = get_history(symbol)
    if hist.empty or len(hist) < 70:
        return None, f"找不到 {query} 的有效指數資料。"
    m = common_metrics(hist)
    scored = score_signal(m, "index")
    cost_info = analyze_cost_plan(m["close"], cost, m["support"], m["resistance"], "index")
    return build_result_dict("指數技術分析", "指數", query, real_symbol, hist, m, scored, cost_info), None


def analyze_commodity(symbol: str, query: str, cost: Optional[float] = None):
    hist, real_symbol = get_history(symbol)
    if hist.empty or len(hist) < 70:
        return None, f"找不到 {query} 的有效原物料資料。"
    m = common_metrics(hist)
    scored = score_signal(m, "commodity")
    cost_info = analyze_cost_plan(m["close"], cost, m["support"], m["resistance"], "commodity")
    return build_result_dict("原物料技術分析", "原物料", query, real_symbol, hist, m, scored, cost_info), None


def analyze_target(query: str, cost: Optional[float] = None):
    symbol = normalize_symbol(query)
    asset_type = detect_asset_type(query, symbol)

    if asset_type == "index":
        return analyze_index(symbol, query, cost)
    if asset_type == "fx":
        return analyze_fx(symbol, query, cost)
    if asset_type == "bond":
        return analyze_bond(symbol, query, cost)
    if asset_type == "commodity":
        return analyze_commodity(symbol, query, cost)

    resolved = resolve_tw_stock_symbol(query)
    if resolved:
        return analyze_stock(resolved["symbol"], query, cost)

    if query.strip().isdigit():
        return analyze_stock(symbol, query, cost)

    suggestions = suggest_tw_stock_names(query, limit=5)
    if suggestions:
        return None, "找不到對應標的，你是不是想查：<br>" + "<br>".join(f"• {x}" for x in suggestions)

    return None, f"找不到「{query}」對應的股票、匯率、指數、原物料或債券資料。"

# =========================================================
# 8) HTML 顯示
# =========================================================
def format_analysis_html(result: dict):
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

    cost_block = ""
    cost_info = result.get("cost_info")
    if cost_info:
        cost_block = f"""
        <div class="section">
            <h3>成本價分析</h3>
            <div class="grid">
                <div class="item"><span>持有成本</span><strong>{cost_info['cost']}</strong></div>
                <div class="item"><span>目前損益</span><strong>{round(cost_info['pnl_pct'], 2)}%</strong></div>
                <div class="item wide"><span>成本建議</span><strong>{cost_info['action']}</strong></div>
                <div class="item wide"><span>支撐觀察</span><strong>{cost_info['support_note']}</strong></div>
                <div class="item wide"><span>壓力觀察</span><strong>{cost_info['resistance_note']}</strong></div>
                <div class="item"><span>參考停損</span><strong>{cost_info['stop_loss_pct']}%</strong></div>
                <div class="item"><span>參考停利</span><strong>{cost_info['take_profit_pct']}%</strong></div>
            </div>
        </div>
        """

    chart_html = result.get("chart_html", "")

    return f"""
    <div class="result-card">
        <div class="result-head">
            <h2>{result.get('title', '查詢結果')}</h2>
            <div class="score {score_class}">綜合分數：{score}</div>
        </div>

        <div class="grid">
            <div class="item"><span>查詢代碼</span><strong>{result.get('symbol')}</strong></div>
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
            <div class="item"><span>近20日支撐</span><strong>{result.get('support')}</strong></div>
            <div class="item"><span>近20日壓力</span><strong>{result.get('resistance')}</strong></div>
            <div class="item"><span>葛蘭碧法則</span><strong>{result.get('granville_rule')}</strong></div>
            <div class="item wide"><span>葛蘭碧判斷</span><strong>{result.get('granville_signal')}</strong></div>
            <div class="item wide"><span>現在狀態</span><strong>{result.get('signal')}</strong></div>
            <div class="item wide"><span>適合動作</span><strong>{result.get('action')}</strong></div>
            <div class="item wide"><span>進場時機</span><strong>{result.get('timing')}</strong></div>
            <div class="item wide"><span>持有者動作</span><strong>{result.get('holder_action')}</strong></div>
        </div>

        <div class="section">
            <h3>葛蘭碧八大法則</h3>
            <ul><li>{result.get('granville_reason')}</li></ul>
        </div>

        <div class="section">
            <h3>判斷依據</h3>
            <ul>{reasons_html}</ul>
        </div>

        <div class="section">
            <h3>風險提醒</h3>
            <ul>{risks_html if risks_html else "<li>無</li>"}</ul>
        </div>

        {cost_block}

        <div class="section">
            <h3>技術圖表</h3>
            {chart_html}
        </div>
    </div>
    """


HTML_TEMPLATE = """
<!doctype html>
<html lang="zh-Hant">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>投資查詢平台</title>
    <style>
        body { margin: 0; font-family: "Microsoft JhengHei", Arial, sans-serif; background: #f5f7fb; color: #1f2937; }
        .container { max-width: 1200px; margin: 30px auto; padding: 20px; }
        .card { background: white; border-radius: 18px; padding: 24px; box-shadow: 0 8px 24px rgba(0,0,0,0.08); margin-bottom: 20px; }
        h1 { margin-top: 0; font-size: 30px; }
        .sub { color: #6b7280; margin-bottom: 18px; }
        form { display: grid; grid-template-columns: 2fr 1fr auto; gap: 12px; }
        input { padding: 14px 16px; border-radius: 12px; border: 1px solid #d1d5db; font-size: 16px; }
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
        ul { margin: 0; padding-left: 20px; line-height: 1.8; }
        .quick-links { margin-top: 12px; display: flex; flex-wrap: wrap; gap: 10px; }
        .quick-links a { display: inline-block; padding: 8px 12px; border-radius: 999px; background: #e0e7ff; color: #3730a3; text-decoration: none; font-size: 14px; }
        @media (max-width: 900px) {
            form { grid-template-columns: 1fr; }
            .grid { grid-template-columns: repeat(2, 1fr); }
            .wide { grid-column: span 2; }
        }
        @media (max-width: 560px) {
            .grid { grid-template-columns: 1fr; }
            .wide { grid-column: span 1; }
        }
    </style>
</head>
<body>
    <div class="container">
        <div class="card">
            <h1>投資查詢平台</h1>
            <div class="sub">支援台股、台灣加權指數、匯率、原物料、債券 ETF、成本價分析、葛蘭碧八大法則、K線圖 + RSI + KD 圖表</div>

            <form method="post">
                <input type="text" name="query" placeholder="例如：台積電、0050、台灣加權指數、美元、黃金、美債" value="{{ query or '' }}" required>
                <input type="number" step="0.0001" name="cost" placeholder="成本價，可不填" value="{{ cost or '' }}">
                <button type="submit">開始查詢</button>
            </form>

            <div class="tips">
                範例：台積電、0050、台灣加權指數、美元、美債、黃金、原油、天然氣、銅。<br>
                成本價可不填；若有填，會多顯示損益與停利停損參考。
            </div>

            <div class="quick-links">
                <a href="/?q=台積電">台積電</a>
                <a href="/?q=0050">0050</a>
                <a href="/?q=台灣加權指數">台灣加權指數</a>
                <a href="/?q=美元">美元</a>
                <a href="/?q=美債">美債</a>
                <a href="/?q=黃金">黃金</a>
                <a href="/?q=原油">原油</a>
                <a href="/?q=銅">銅</a>
            </div>
        </div>

        {% if error %}
        <div class="error">{{ error|safe }}</div>
        {% endif %}

        {% if result_html %}
            {{ result_html|safe }}
        {% endif %}
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

    if request.method == "GET":
        query = (request.args.get("q") or "").strip()
        cost = (request.args.get("cost") or "").strip()
    else:
        query = (request.form.get("query") or "").strip()
        cost = (request.form.get("cost") or "").strip()

    if query:
        parsed_cost = None
        if cost:
            try:
                parsed_cost = float(cost)
            except ValueError:
                error = "成本價格式錯誤，請輸入數字。"

        if error is None:
            result, err = analyze_target(query, parsed_cost)
            if err:
                error = err
            else:
                result_html = format_analysis_html(result)

    return render_template_string(
        HTML_TEMPLATE,
        result_html=result_html,
        error=error,
        query=query,
        cost=cost,
    )


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 10000))
    app.run(host="0.0.0.0", port=port, debug=False)
