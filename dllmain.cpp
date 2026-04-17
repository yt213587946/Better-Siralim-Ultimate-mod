#include "pch.h"
#include <windows.h>
#include "MinHook.h"
#include <string>
#include <sstream>
#include <vector>
#include <atomic>
#include <mutex>
#include <algorithm>
#include <intrin.h>

// ============================================================
// 数据结构
// ============================================================

struct RValue {
    union {
        double   v_double;
        long long v_int64;
        void* ptr;
    } value;
    int flags;
    int type; // 0=Double,1=String,2=Array,7=Int32,10=Int64,15=Instance
};

struct ModInfo {
    const char* name;
    const char* version;
    const char* author;
};

struct ModLoaderAPI {
    uintptr_t(*FindPattern)(const char* pattern);
    void(*Log)(const char* text);
};

static ModLoaderAPI* g_api = nullptr;

// ============================================================
// 地址工具
// ============================================================

static uintptr_t GetGameModuleBase()
{
    return (uintptr_t)GetModuleHandleW(nullptr);
}

static constexpr uintptr_t kGameImageBase = 0x140000000ULL;

static uintptr_t AddrFromImageVa(uintptr_t imageVa)
{
    if (imageVa < kGameImageBase) return 0;
    return GetGameModuleBase() + (imageVa - kGameImageBase);
}

template<typename T = void>
static T* PtrFromImageVa(uintptr_t imageVa)
{
    return (T*)AddrFromImageVa(imageVa);
}

// ============================================================
// 反编译符号地址
// ============================================================

static constexpr uintptr_t kFUN_1478bbd70 = 0x1478BBD70ULL;

static constexpr uintptr_t kFUN_14028c410 = 0x14028C410ULL;
static constexpr uintptr_t kFUN_14028c630 = 0x14028C630ULL;

// ============================================================
// 函数指针类型 & 原函数指针
// ============================================================

typedef void* (__fastcall* GML_LoadCreature_Fn)(void*, void*, RValue*, int, RValue**);
typedef void* (__fastcall* GML_ScrFuse_Fn)(void*, void*, RValue*, int, RValue**);
typedef void* (__fastcall* GML_NetherStoneCreate_Fn)(void*, void*, RValue*, int, RValue**);
typedef void* (__fastcall* GML_Roll_Fn)(void*, void*, RValue*, int, RValue**);
typedef void* (__fastcall* GML_LootBox_Fn)(void*, void*, RValue*, int, RValue**);
typedef void* (__fastcall* GML_Script_SG)(void*, void*, RValue*, int, RValue**);
typedef void* (__fastcall* GML_Script_Fn)(void*, void*, RValue*);
typedef void* (__fastcall* GML_Script_Ek)(void*, void*);
typedef void* (__fastcall* GML_InvLoot_Fn)(void*, void*, RValue*, int, RValue**);
typedef void* (__fastcall* CreateMiscFunc)(void*, void*, RValue*, int, RValue**);
typedef void* (__fastcall* CreateMaterialFunc)(void*, void*, RValue*, int, RValue**);
typedef void* (__fastcall* GML_TalismanMaxRank_Fn)(void*, void*, RValue*, int, RValue**);

typedef uint64_t(__fastcall* Fn_ReadVarById)(
    void* targetRValue,
    uint32_t varId,
    uint32_t flags,
    void* outRValue,
    void* arg5,
    void* arg6);

typedef void* (__fastcall* GML_Assign410_Fn)(RValue* dest, void* src);
typedef void* (__fastcall* GML_Assign630_Fn)(RValue* dest, void* src);

static GML_Assign410_Fn pOriginalAssign410 = nullptr;
static GML_Assign630_Fn pOriginalAssign630 = nullptr;

static GML_LoadCreature_Fn      pOriginalLoadCreature = nullptr;
static GML_ScrFuse_Fn           pOriginalScrFuse = nullptr;
static GML_NetherStoneCreate_Fn pOriginalNetherStoneCreate = nullptr;
static GML_Roll_Fn              pOriginalScrRoll = nullptr;
static GML_LootBox_Fn           pOriginalLootBox = nullptr;
static GML_Script_SG            pOriginalFavor = nullptr;
static GML_Script_Fn            pOriginalResources = nullptr;
static GML_Script_Fn            pOriginalGetLevel = nullptr;
static GML_InvLoot_Fn           pOriginalInvLoot = nullptr;
static GML_Script_Ek            pOriginalEmblemKeyPress = nullptr;
static GML_Script_Ek            pOriginalMaterialKeyPress = nullptr;
static CreateMiscFunc           pOriginalCreateMisc = nullptr;
static CreateMaterialFunc       pOriginalCreateMaterial = nullptr;
static Fn_ReadVarById           pReadVarById = nullptr;
static GML_TalismanMaxRank_Fn pOriginalTalismanMaxRank = nullptr;

// ============================================================
// 状态变量
// ============================================================

static std::atomic<bool>     g_EmblemActive(false);
static std::atomic<bool>     g_InExtra(false);
static std::atomic<int>      g_LastEmblemID(-1);
static std::atomic<bool>     g_MaterialActive(false);
static std::atomic<int>      g_LastMaterialID(-1);
static std::atomic<bool>     g_InNetherStoneCreate(false);
static std::atomic<int>      g_NetherStoneHighestLevel(1);
static std::atomic<int>      g_NetherStoneBonusTenths(0);

// ============================================================
// 内存安全工具
// ============================================================

static bool IsProbablyReadablePtr(const void* p)
{
    if (!p) return false; MEMORY_BASIC_INFORMATION mbi{};
    if (VirtualQuery(p, &mbi, sizeof(mbi)) == 0) return false;
    if (mbi.State != MEM_COMMIT) return false;
    DWORD prot = mbi.Protect & 0xff;
    return !(prot == PAGE_NOACCESS || prot == PAGE_GUARD);
}

static bool IsReadableRange(const void* p, size_t size)
{
    if (!p || size == 0) return false;
    const unsigned char* cur = (const unsigned char*)p;
    const unsigned char* end = cur + size;
    while (cur < end)
    {
        MEMORY_BASIC_INFORMATION mbi{};
        if (VirtualQuery(cur, &mbi, sizeof(mbi)) == 0) return false;
        if (mbi.State != MEM_COMMIT) return false;
        DWORD prot = mbi.Protect & 0xff;
        if (prot == PAGE_NOACCESS || prot == PAGE_GUARD) return false;
        const unsigned char* regionEnd = (const unsigned char*)mbi.BaseAddress + mbi.RegionSize;
        if (regionEnd <= cur) return false;
        cur = (regionEnd < end) ? regionEnd : end;
    }
    return true;
}

// ============================================================
// RewardResources 定向后处理上下文
// ============================================================

struct RewardCaptureContext
{
    bool active = false;              // 当前线程是否位于 bc_GetRewardResources
    bool suppressCapture = false;     // 后处理阶段避免再次捕获
    uintptr_t stackLow = 0;           // 当前线程栈下界
    uintptr_t stackHigh = 0;          // 当前线程栈上界
    std::vector<RValue*> writeOrder;  // 记录执行期间“非栈数值目标”的写入顺序
};

static thread_local RewardCaptureContext g_rewardCtx;

// ============================================================
// RewardResources 工具
// ============================================================

static bool IsNumericRValue(const RValue* v)
{
    return v && (v->type == 0 || v->type == 7 || v->type == 10);
}

static bool QueryCurrentThreadStackRange(uintptr_t* outLow, uintptr_t* outHigh)
{
    if (!outLow || !outHigh) return false;

    typedef VOID(WINAPI* FnGetCurrentThreadStackLimits)(PULONG_PTR, PULONG_PTR);
    static FnGetCurrentThreadStackLimits pGetCurrentThreadStackLimits =
        (FnGetCurrentThreadStackLimits)GetProcAddress(
            GetModuleHandleW(L"kernel32.dll"),
            "GetCurrentThreadStackLimits");

    if (pGetCurrentThreadStackLimits)
    {
        ULONG_PTR low = 0, high = 0;
        pGetCurrentThreadStackLimits(&low, &high);
        *outLow = (uintptr_t)low;
        *outHigh = (uintptr_t)high;
        return true;
    }

    // fallback：以局部变量为中心估算 ±2MB 栈窗口
    char marker = 0;
    uintptr_t p = (uintptr_t)&marker;
    *outLow = (p > 0x200000) ? (p - 0x200000) : 0;
    *outHigh = p + 0x200000;
    return true;
}

static bool IsPtrOnCurrentStack(const void* p)
{
    if (!p || !g_rewardCtx.active) return false;
    uintptr_t a = (uintptr_t)p;
    return a >= g_rewardCtx.stackLow && a < g_rewardCtx.stackHigh;
}

static void ScaleRValueInPlace(RValue* v, double factor)
{
    if (!v) return;

    if (v->type == 0)
    {
        v->value.v_double *= factor;
    }
    else if (v->type == 7 || v->type == 10)
    {
        v->value.v_int64 = (long long)((double)v->value.v_int64 * factor);
    }
}

static std::vector<RValue*> CollectLastUniqueTargets(const std::vector<RValue*>& order, size_t wantCount)
{
    std::vector<RValue*> out;
    out.reserve(wantCount);

    for (auto it = order.rbegin(); it != order.rend(); ++it)
    {
        RValue* p = *it;
        if (!p) continue;

        bool exists = false;
        for (RValue* e : out)
        {
            if (e == p)
            {
                exists = true;
                break;
            }
        }

        if (!exists)
        {
            out.push_back(p);
            if (out.size() >= wantCount)
                break;
        }
    }

    std::reverse(out.begin(), out.end());
    return out;
}

static void LogRewardTargets(const char* title, const std::vector<RValue*>& targets)
{
    if (!g_api) return;

    char buf[256];
    sprintf_s(buf, "%s: %zu target(s)", title, targets.size());
    g_api->Log(buf);

    for (size_t i = 0; i < targets.size(); ++i)
    {
        const RValue* v = targets[i];
        if (!v || !IsReadableRange(v, sizeof(RValue)))
            continue;

        if (v->type == 0)
            sprintf_s(buf, "  [%zu] %p type=double value=%.3f", i, (const void*)v, v->value.v_double);
        else if (v->type == 7 || v->type == 10)
            sprintf_s(buf, "  [%zu] %p type=int value=%lld", i, (const void*)v, (long long)v->value.v_int64);
        else
            sprintf_s(buf, "  [%zu] %p type=%d", i, (const void*)v, v->type);

        g_api->Log(buf);
    }
}

// ============================================================
// 字符串工具
// ============================================================

static bool LooksLikePrintableAscii(const char* s, size_t maxCheck = 64)
{
    if (!s || !IsReadableRange(s, 1)) return false;
    for (size_t i = 0; i < maxCheck; ++i)
    {
        if (!IsReadableRange(s + i, 1)) return false; unsigned char c = (unsigned char)s[i];
        if (c == 0) return i > 0;
        if (!(c == 9 || c == 10 || c == 13 || (c >= 32 && c <= 126))) return false;
    }
    return true;
}

static std::string ReadAsciiStringSafe(const char* s, size_t maxLen = 120)
{
    if (!s || !IsReadableRange(s, 1)) return "";
    std::string out;
    for (size_t i = 0; i < maxLen; ++i)
    {
        if (!IsReadableRange(s + i, 1)) break;
        unsigned char c = (unsigned char)s[i];
        if (c == 0) break;
        if (c == '\r') out += "\\r";
        else if (c == '\n') out += "\\n";
        else if (c == '\t') out += "\\t";
        else if (c >= 32 && c <= 126) out.push_back((char)c);
        else out.push_back('?');
    }
    return out;
}

static bool LooksLikePrintableWide(const wchar_t* s, size_t maxCheck = 64)
{
    if (!s || !IsReadableRange(s, sizeof(wchar_t))) return false;
    for (size_t i = 0; i < maxCheck; ++i)
    {
        if (!IsReadableRange(s + i, sizeof(wchar_t))) return false;
        wchar_t c = s[i];
        if (c == 0) return i > 0;
        if (!(c == L'\t' || c == L'\n' || c == L'\r' || (c >= 32 && c <= 126))) return false;
    }
    return true;
}

static std::string ReadWideStringSafe(const wchar_t* s, size_t maxLen = 120)
{
    if (!s || !IsReadableRange(s, sizeof(wchar_t))) return "";
    std::string out;
    for (size_t i = 0; i < maxLen; ++i)
    {
        if (!IsReadableRange(s + i, sizeof(wchar_t))) break;
        wchar_t c = s[i];
        if (c == 0) break;
        if (c == L'\r') out += "\\r";
        else if (c == L'\n') out += "\\n";
        else if (c == L'\t') out += "\\t";
        else if (c >= 32 && c <= 126) out.push_back((char)c);
        else out.push_back('?');
    }
    return out;
}

static bool LooksLikeUtf8String(const char* s, size_t maxCheck = 64)
{
    if (!s || !IsReadableRange(s, 1)) return false;
    size_t i = 0;
    while (i < maxCheck)
    {
        if (!IsReadableRange(s + i, 1)) return false;
        unsigned char c = (unsigned char)s[i];
        if (c == 0) return i > 0;
        if (c == 9 || c == 10 || c == 13 || (c >= 32 && c <= 126)) { ++i; continue; }
        int extra = 0;
        if ((c & 0xE0) == 0xC0) extra = 1;
        else if ((c & 0xF0) == 0xE0) extra = 2;
        else if ((c & 0xF8) == 0xF0) extra = 3;
        else return false;
        for (int j = 1; j <= extra; ++j)
        {
            if (!IsReadableRange(s + i + j, 1)) return false;
            if (((unsigned char)s[i + j] & 0xC0) != 0x80) return false;
        }
        i += 1 + extra;
    }
    return true;
}

static std::string ReadUtf8StringSafe(const char* s, size_t maxLen = 256)
{
    if (!s || !IsReadableRange(s, 1)) return "";
    std::string out;
    for (size_t i = 0; i < maxLen; ++i)
    {
        if (!IsReadableRange(s + i, 1)) break;
        unsigned char c = (unsigned char)s[i];
        if (c == 0) break;
        if (c == '\r') out += "\\r";
        else if (c == '\n') out += "\\n";
        else if (c == '\t') out += "\\t";
        else out.push_back((char)c);
    }
    return out;
}

// ============================================================
// YYString 解析
// ============================================================

static std::string TryReadYYCString(const void* yyStrPtr)
{
    if (!yyStrPtr || !IsReadableRange(yyStrPtr, 0x20)) return "";

    const char* base = (const char*)yyStrPtr;
    const uint64_t off00 = *(const uint64_t*)(base + 0x00);
    const uint64_t off08 = *(const uint64_t*)(base + 0x08);
    const uint32_t len = (uint32_t)(off08 >> 32);

    // 路径 A：+0x00 指向自身附近（内联指针）
    {
        const char* dataPtr = (const char*)off00;
        bool isInline = off00 != 0
            && (uintptr_t)dataPtr >= (uintptr_t)base
            && (uintptr_t)dataPtr <= (uintptr_t)base + 0x20;
        if (isInline && IsProbablyReadablePtr(dataPtr))
        {
            size_t readLen = (len > 0 && len < 4096) ? len + 1 : 256;
            if (IsReadableRange(dataPtr, readLen) && LooksLikeUtf8String(dataPtr, readLen))
            {
                std::string s = ReadUtf8StringSafe(dataPtr, readLen);
                if (!s.empty()) return s;
            }
        }
    }

    // 路径 B：+0x00 指向外部堆字符串
    {
        const char* dataPtr = (const char*)off00;
        if (dataPtr && IsProbablyReadablePtr(dataPtr) && LooksLikeUtf8String(dataPtr, 256))
        {
            std::string s = ReadUtf8StringSafe(dataPtr, 256);
            if (!s.empty()) return s;
        }
    }

    // 路径 C：+0x10 内联兜底
    {
        const char* inlineStr = base + 0x10;
        size_t readLen = (len > 0 && len < 4096) ? len + 1 : 64;
        if (IsReadableRange(inlineStr, readLen) && LooksLikeUtf8String(inlineStr, readLen))
        {
            std::string s = ReadUtf8StringSafe(inlineStr, readLen);
            if (!s.empty()) return s;
        }
    }

    return "";
}

static std::string TryExtractStringFromPtr(const void* p)
{
    if (!p || !IsProbablyReadablePtr(p)) return "";

    //尝试作为 YYString 对象
    if (IsReadableRange(p, 0x20))
    {
        std::string s = TryReadYYCString(p);
        if (!s.empty()) return s;
    }

    // 直接 ASCII
    const char* a = (const char*)p;
    if (LooksLikePrintableAscii(a)) { std::string s = ReadAsciiStringSafe(a); if (!s.empty()) return s; }

    // 直接 Wide
    const wchar_t* w = (const wchar_t*)p;
    if (LooksLikePrintableWide(w)) { std::string s = ReadWideStringSafe(w); if (!s.empty()) return s; }

    // 一级解引用
    if (IsReadableRange(p, sizeof(void*)))
    {
        void* inner = *(void* const*)p;
        if (inner && IsProbablyReadablePtr(inner))
        {
            const char* ia = (const char*)inner;
            if (LooksLikePrintableAscii(ia)) { std::string s = ReadAsciiStringSafe(ia); if (!s.empty()) return s; }
        }
    }

    return "";
}

// ============================================================
// RValue 工具
// ============================================================

static double RValueToDoubleSafe(const RValue* v, double def = 0.0)
{
    if (!v) return def;
    switch (v->type)
    {
    case 0:return v->value.v_double;
    case 7:
    case 10: return (double)v->value.v_int64;
    default: return def;
    }
}

static int RValueToIntSafe(const RValue* v, int def = -1)
{
    if (!v) return def;
    switch (v->type)
    {
    case 0:  return (int)v->value.v_double;
    case 7:
    case 10: return (int)v->value.v_int64;
    default: return def;
    }
}

static std::string RValueToSimpleText(const RValue* v)
{
    if (!v) return "<null>";
    char buf[64];
    switch (v->type)
    {
    case 0:  sprintf_s(buf, "%.0f", v->value.v_double); return buf;
    case 7:
    case 10: sprintf_s(buf, "%lld", (long long)v->value.v_int64); return buf;
    case 1: { auto s = TryExtractStringFromPtr(v->value.ptr); return s.empty() ? "<string>" : s; }
    default: sprintf_s(buf, "type=%d", v->type); return buf;
    }
}

static std::string DescribeRValueForField(const RValue* v)
{
    if (!v) return "<null>";
    if (v->type == 1)
    {
        auto s = TryExtractStringFromPtr(v->value.ptr);
        if (!s.empty()) return s;
    }
    return RValueToSimpleText(v);
}

// ============================================================
// 数组工具
// ============================================================

static int GetArraySizeSafe(const RValue* a)
{
    if (!a || a->type != 2 || !a->value.ptr) return -1;
    auto* arr = (unsigned char*)a->value.ptr;
    if (!IsReadableRange(arr, 0x28)) return -1;
    return *(int*)(arr + 0x24);
}

static bool GetArrayElementSafe(const RValue* a, int idx, RValue* out)
{
    if (!a || !out || a->type != 2 || !a->value.ptr) return false;
    auto* arr = (unsigned char*)a->value.ptr;
    if (!IsReadableRange(arr, 0x28)) return false;
    int size = *(int*)(arr + 0x24);
    if (idx < 0 || idx >= size) return false;
    auto* data = *(unsigned char**)(arr + 8);
    if (!data) return false;
    size_t offs = (size_t)idx * sizeof(RValue);
    if (!IsReadableRange(data + offs, sizeof(RValue))) return false;
    *out = *(RValue*)(data + offs);
    return true;
}

// ============================================================
// ReadGameVar
// ============================================================

static bool ReadGameVar(const RValue* target, uint32_t varId, RValue* out)
{
    if (!pReadVarById || !target || !out || varId == 0) return false;

    memset(out, 0, sizeof(RValue));
    out->type = 5;

    if (target->type == 15)
    {
        // type=15: instance handle，低32位是 instance id
        //构造 type=7 临时 RValue，走 FUN_1478bbd70 的int分支
        RValue tmp{};
        tmp.type = 7;
        tmp.flags = 0;
        tmp.value.v_int64 = (int)(target->value.v_int64 & 0xFFFFFFFF);
        pReadVarById(&tmp, varId, 0x80000000, out, nullptr, nullptr);
        return true;
    }

    pReadVarById((void*)target, varId, 0x80000000, out, nullptr, nullptr);
    return true;
}

static uint32_t ReadVarIdFromImageVa(uintptr_t imageVa)
{
    auto* p = PtrFromImageVa<uint32_t>(imageVa);
    if (!p || !IsReadableRange(p, sizeof(uint32_t))) return 0;
    return *p;
}

// ============================================================
// 辅助：获取玩家最高等级
// ============================================================

static int GetHighestPlayerCreatureLevel(void* p1, void* p2)
{
    if (!pOriginalGetLevel) return 1;
    RValue result{};
    result.type = 5;
    result.value.v_int64 = 0;
    pOriginalGetLevel(p1, p2, &result);
    int lv = RValueToIntSafe(&result, 1);
    return lv > 0 ? lv : 1;
}

// ============================================================
// Hook：赋值拦截
// ============================================================

static void CaptureRewardWriteTarget(RValue* dest)
{
    if (!g_rewardCtx.active || g_rewardCtx.suppressCapture)
        return;

    if (!dest)
        return;

    if (!IsReadableRange(dest, sizeof(RValue)))
        return;

    if (!IsNumericRValue(dest))
        return;

    if (IsPtrOnCurrentStack(dest))
        return;

    g_rewardCtx.writeOrder.push_back(dest);
}

static void* __fastcall HookedAssign410(RValue* dest, void* src)
{
    void* ret = pOriginalAssign410(dest, src);
    CaptureRewardWriteTarget(dest);
    return ret;
}

static void* __fastcall HookedAssign630(RValue* dest, void* src)
{
    void* ret = pOriginalAssign630(dest, src);
    CaptureRewardWriteTarget(dest);
    return ret;
}

// ============================================================
// Hook：恩惠
// ============================================================

static void* __fastcall HookedGodAddFavor(void* p1, void* p2, RValue* res, int argc, RValue** args)
{
    if (argc >= 2 && args[1])
    {
        RValue boosted = *args[1];
        if (boosted.type == 0) boosted.value.v_double *= 10.0;
        else                boosted.value.v_int64 *= 10;
        RValue* modArgs[2] = { args[0], &boosted };
        return pOriginalFavor(p1, p2, res, 2, modArgs);
    }
    return pOriginalFavor(p1, p2, res, argc, args);
}

// ============================================================
// Hook：资源
// ============================================================

static void* __fastcall HookedGetRewardResources(void* p1, void* p2, RValue* p3)
{
    static double g_RewardResourceMultiplier = 4.0;

    // 防止意外重入
    if (g_rewardCtx.active)
        return pOriginalResources(p1, p2, p3);

    g_rewardCtx.active = true;
    g_rewardCtx.suppressCapture = false;
    g_rewardCtx.writeOrder.clear();
    QueryCurrentThreadStackRange(&g_rewardCtx.stackLow, &g_rewardCtx.stackHigh);

    void* ret = pOriginalResources(p1, p2, p3);

    // 关闭捕获，开始后处理
    g_rewardCtx.suppressCapture = true;

    // 按“最后 5 个唯一非栈数值目标”作为最终 reward slot
    std::vector<RValue*> targets = CollectLastUniqueTargets(g_rewardCtx.writeOrder, 5);

    if (targets.size() == 5)
    {
        //if (g_api)g_api->Log("RewardResources: captured 5 final reward targets, applying x2 post-scale.");

        for (RValue* v : targets)
        {
            if (!v || !IsReadableRange(v, sizeof(RValue)))
                continue;

            ScaleRValueInPlace(v, g_RewardResourceMultiplier);
        }

        //LogRewardTargets("RewardResources post-scale targets", targets);
    }
    else
    {
        if (g_api)
        {
            char buf[128];
            sprintf_s(buf,
                "RewardResources: target capture mismatch, expected 5 got %zu; post-scale skipped.",
                targets.size());
            g_api->Log(buf);
        }
    }

    g_rewardCtx.writeOrder.clear();
    g_rewardCtx.stackLow = 0;
    g_rewardCtx.stackHigh = 0;
    g_rewardCtx.suppressCapture = false;
    g_rewardCtx.active = false;

    return ret;
}

// ============================================================
// Hook：材料按键
// ============================================================

static void* __fastcall HookedMaterialKeyPress(void* p1, void* p2)
{
    if (g_InExtra) return pOriginalMaterialKeyPress(p1, p2);
    g_MaterialActive = true;
    void* r = pOriginalMaterialKeyPress(p1, p2);
    g_MaterialActive = false;
    return r;
}

// ============================================================
// Hook：勋章按键
// ============================================================

static void* __fastcall HookedEmblemKeyPress(void* p1, void* p2)
{
    if (g_InExtra) return pOriginalEmblemKeyPress(p1, p2);
    g_EmblemActive = true;
    void* r = pOriginalEmblemKeyPress(p1, p2);
    g_EmblemActive = false;
    return r;
}

// ============================================================
// Hook：CreateMisc（记录勋章 ID）
// ============================================================

static void* __fastcall HookedCreateMisc(void* p1, void* p2, RValue* res, int argc, RValue** args)
{
    if (g_EmblemActive && argc >= 1 && args && args[0])
    {
        RValue* a = args[0];
        if (a->type == 7 || a->type == 10) g_LastEmblemID = (int)a->value.v_int64;
        else if (a->type == 0)g_LastEmblemID = (int)a->value.v_double;
    }
    return pOriginalCreateMisc(p1, p2, res, argc, args);
}

// ============================================================
// Hook：CreateMaterial（记录材料 ID）
// ============================================================

static void* __fastcall HookedCreateMaterial(void* p1, void* p2, RValue* res, int argc, RValue** args)
{
    if (g_MaterialActive && argc >= 1 && args && args[0])
    {
        RValue* a = args[0];
        if (a->type == 7 || a->type == 10) g_LastMaterialID = (int)a->value.v_int64;
        else if (a->type == 0)             g_LastMaterialID = (int)a->value.v_double;
    }
    return pOriginalCreateMaterial(p1, p2, res, argc, args);
}

// ============================================================
// Hook：LootBox
// ============================================================

static void* __fastcall HookedLootBox(void* p1, void* p2, RValue* res, int argc, RValue** args)
{
    void* result = pOriginalLootBox(p1, p2, res, argc, args);

    //勋章
    if (g_EmblemActive && !g_InExtra && g_LastEmblemID >= 0)
    {
        g_InExtra = true;
        int lv = GetHighestPlayerCreatureLevel(p1, p2);
        int extra = lv / 20;
        if (extra > 25) extra = 25;
        int total = 4 + extra;

        if (g_api) {
            char buf[256];
            sprintf_s(buf, sizeof(buf),
                ">>> LootBox: level=%d extra_mult=%d total_emblems=%d (id=%d)",
                lv, extra, total + 1, (int)g_LastEmblemID.load());
            g_api->Log(buf);
        }

        for (int i = 0; i < total; ++i)
        {
            RValue eid{}; eid.type = 7; eid.value.v_int64 = g_LastEmblemID;
            RValue* ep = &eid;
            RValue newItem{}; newItem.type = 5;
            pOriginalCreateMisc(p1, p2, &newItem, 1, &ep);
            RValue* ip = &newItem;
            pOriginalLootBox(p1, p2, res, 1, &ip);
        }

        g_InExtra = false;
        g_LastEmblemID = -1;
    }

    // 材料
    if (g_MaterialActive && !g_InExtra && g_LastMaterialID >= 0)
    {
        g_InExtra = true;

        if (g_api) {
            char buf[128];
            sprintf_s(buf, sizeof(buf),
                ">>> LootBox: giving4 extra materials (id=%d)",
                (int)g_LastMaterialID.load());
            g_api->Log(buf);
        }

        for (int i = 0; i < 4; ++i)
        {
            RValue mid{}; mid.type = 7; mid.value.v_int64 = g_LastMaterialID;
            RValue* mp = &mid;
            RValue newMat{}; newMat.type = 5;
            pOriginalCreateMaterial(p1, p2, &newMat, 1, &mp);
            RValue* ip = &newMat;
            pOriginalLootBox(p1, p2, res, 1, &ip);
        }

        g_InExtra = false;
        g_LastMaterialID = -1;
    }

    return result;
}

// ============================================================
// Hook：InvLoot（战利品数量 ×3）
// ============================================================

static void* __fastcall HookedInvLoot(void* p1, void* p2, RValue* res, int argc, RValue** args)
{
    if (argc >= 2 && args && args[1])
    {
        RValue* q = args[1];
        double orig = (q->type == 0) ? q->value.v_double : (double)q->value.v_int64;
        q->type = 0;
        q->value.v_double = orig * 3.0;
    }
    return pOriginalInvLoot(p1, p2, res, argc, args);
}

// ============================================================
// Hook：NetherStoneCreate
// ============================================================

static void* __fastcall HookedNetherStoneCreate(void* p1, void* p2, RValue* res, int argc, RValue** args)
{
    bool outermost = !g_InNetherStoneCreate.load();
    if (outermost)
    {
        int lv = GetHighestPlayerCreatureLevel(p1, p2);
        if (lv < 1) lv = 1;
        g_NetherStoneHighestLevel = lv;
        g_NetherStoneBonusTenths = lv / 10;
        g_InNetherStoneCreate = true;

        if (g_api) {
            char buf[128];
            sprintf_s(buf, sizeof(buf),
                "NetherStone context entered: highestLevel=%d bonus=%d", lv, lv / 10);
            g_api->Log(buf);
        }
    }

    void* ret = pOriginalNetherStoneCreate(p1, p2, res, argc, args);

    if (outermost)
    {
        g_InNetherStoneCreate = false;
        g_NetherStoneHighestLevel = 1;
        g_NetherStoneBonusTenths = 0;
    }
    return ret;
}

// ============================================================
// Hook：ScrRoll（NetherStone 概率调整）
// ============================================================

static void* __fastcall HookedScrRoll(void* p1, void* p2, RValue* res, int argc, RValue** args)
{
    if (g_InNetherStoneCreate.load() && argc >= 1 && args && args[0])
    {
        RValue mod = *args[0];
        double old = (mod.type == 0) ? mod.value.v_double : (double)mod.value.v_int64;
        double bonus = (double)g_NetherStoneBonusTenths.load();
        double nw = old + bonus;
        if (nw > 100.0) nw = 100.0;
        if (nw < 0.0)nw = 0.0;
        mod.type = 0; mod.value.v_double = nw;
        RValue* ma[1] = { &mod };

        if (g_api) {
            char buf[128];
            sprintf_s(buf, sizeof(buf),
                "scr_Roll adjusted: old=%.2f bonus=%.2f new=%.2f", old, bonus, nw);
            g_api->Log(buf);
        }return pOriginalScrRoll(p1, p2, res, 1, ma);
    }
    return pOriginalScrRoll(p1, p2, res, argc, args);
}

// ============================================================
// Hook：inv_TalismanMaxRank（护符最大等级 ×2）
// ============================================================

static void* __fastcall HookedTalismanMaxRank(
    void* p1,
    void* p2,
    RValue* res,
    int     argc,
    RValue** args)
{
    // 先调用原函数，让它正常填充 res
    void* ret = pOriginalTalismanMaxRank(p1, p2, res, argc, args);

    if (res && res->type == 0)
    {
        double maxRank = res->value.v_double;

        // 仅对有效等级（> 1.0）翻倍，-1.0（未找到）和 1.0（最低档）跳过
        if (maxRank > 1.0)
        {
            res->value.v_double = maxRank * 2.0;

            if (g_api)
            {
                char buf[128];
                sprintf_s(buf, sizeof(buf),
                    "TalismanMaxRank: %.1f -> %.1f",
                    maxRank, res->value.v_double);
                g_api->Log(buf);
            }
        }
    }

    return ret;
}

// 内存写入工具

static bool WriteMemoryBytes(uintptr_t addr, const void* data, size_t size)
{
    if (!addr || !data || size == 0) return false; DWORD old;
    if (!VirtualProtect((LPVOID)addr, size, PAGE_EXECUTE_READWRITE, &old)) return false;
    memcpy((void*)addr, data, size);
    FlushInstructionCache(GetCurrentProcess(), (LPCVOID)addr, size);
    DWORD tmp;
    VirtualProtect((LPVOID)addr, size, old, &tmp);
    return true;
}

static void WriteAbsJump14(uintptr_t src, uintptr_t dst, size_t overwriteLen)
{
    if (overwriteLen < 14) return;
    DWORD old;
    VirtualProtect((LPVOID)src, overwriteLen, PAGE_EXECUTE_READWRITE, &old);
    unsigned char* p = (unsigned char*)src;
    p[0] = 0xFF; p[1] = 0x25; p[2] = p[3] = p[4] = p[5] = 0x00;
    *(uintptr_t*)(p + 6) = dst;
    for (size_t i = 14; i < overwriteLen; ++i) p[i] = 0x90;
    VirtualProtect((LPVOID)src, overwriteLen, old, &old);
    FlushInstructionCache(GetCurrentProcess(), (LPCVOID)src, overwriteLen);
}

static uintptr_t BuildNetherStoneLimitStub(uintptr_t site, int32_t stackDisp, uint64_t newBits)
{
    constexpr size_t kLen = 19;
    uintptr_t retAddr = site + kLen;
    int32_t ripDisp = *(int32_t*)(site + 15);
    uintptr_t xmm2Src = retAddr + ripDisp;

    auto* stub = (unsigned char*)VirtualAlloc(nullptr, 0x100, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
    if (!stub) return 0;
    size_t i = 0;

    stub[i++] = 0x50;// push rax
    stub[i++] = 0x48; stub[i++] = 0xB8;// mov rax, newBits
    *(uint64_t*)(stub + i) = newBits; i += 8;
    stub[i++] = 0x48; stub[i++] = 0x89; stub[i++] = 0x85;    // mov [rbp+stackDisp], rax
    *(int32_t*)(stub + i) = stackDisp; i += 4;
    stub[i++] = 0x41; stub[i++] = 0xB1; stub[i++] = 0x01;    // mov r9b, 1
    stub[i++] = 0x48; stub[i++] = 0xB8;                     // mov rax, xmm2Src
    *(uintptr_t*)(stub + i) = xmm2Src; i += 8;
    stub[i++] = 0xF2; stub[i++] = 0x0F; stub[i++] = 0x10; stub[i++] = 0x10; // movsd xmm2,[rax]
    stub[i++] = 0x58;                                     // pop rax
    stub[i++] = 0xFF; stub[i++] = 0x25;                     // jmp [rip+0]
    stub[i++] = stub[i++] = stub[i++] = stub[i++] = 0x00; *(uintptr_t*)(stub + i) = retAddr; i += 8;

    FlushInstructionCache(GetCurrentProcess(), stub, i);
    return (uintptr_t)stub;
}

static bool PatchNetherStoneLimit(uintptr_t site, int32_t stackDisp, uint64_t newBits)
{
    uintptr_t stub = BuildNetherStoneLimitStub(site, stackDisp, newBits);
    if (!stub) return false;
    WriteAbsJump14(site, stub, 19);
    return true;
}

static uintptr_t BuildSetRspDoubleStub(uintptr_t site, uint8_t rspDisp, uint64_t newBits)
{
    constexpr size_t kLen = 14;
    uintptr_t retAddr = site + kLen;

    auto* stub = (unsigned char*)VirtualAlloc(nullptr, 0x100, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
    if (!stub) return 0;
    size_t i = 0;

    stub[i++] = 0x48; stub[i++] = 0xB8;                     // mov rax, newBits
    *(uint64_t*)(stub + i) = newBits; i += 8;
    stub[i++] = 0x66; stub[i++] = 0x48; stub[i++] = 0x0F; stub[i++] = 0x6E; stub[i++] = 0xC0; // movq xmm0,rax
    stub[i++] = 0xF2; stub[i++] = 0x0F; stub[i++] = 0x11; stub[i++] = 0x44; stub[i++] = 0x24; stub[i++] = rspDisp; // movsd [rsp+d],xmm0
    stub[i++] = 0xFF; stub[i++] = 0x25;
    stub[i++] = stub[i++] = stub[i++] = stub[i++] = 0x00;
    *(uintptr_t*)(stub + i) = retAddr; i += 8;

    FlushInstructionCache(GetCurrentProcess(), stub, i);
    return (uintptr_t)stub;
}

static bool PatchSetRspDouble(uintptr_t site, uint8_t rspDisp, uint64_t newBits)
{
    uintptr_t stub = BuildSetRspDoubleStub(site, rspDisp, newBits);
    if (!stub) return false;
    WriteAbsJump14(site, stub, 14);
    return true;
}

static bool PatchJccRel32ToFallthrough(uintptr_t addr)
{
    if (!addr) return false;
    unsigned char* p = (unsigned char*)addr;
    if (p[0] != 0x0F || (p[1] & 0xF0) != 0x80) return false;
    unsigned char patch[6] = { 0xE9, 0x01,0x00,0x00,0x00, 0x90 };
    return WriteMemoryBytes(addr, patch, sizeof(patch));
}

// ============================================================
// 导出
// ============================================================

extern "C" __declspec(dllexport) ModInfo* GetModInfo()
{
    static ModInfo info = { "Better Game", "1.1", "紫心醉梦" };
    return &info;
}

extern "C" __declspec(dllexport) void InitializeMod(ModLoaderAPI* api)
{
    g_api = api;
    if (MH_Initialize() != MH_OK) return;

    // AOB 特征码
    const char* resAOB = "41 54 41 55 41 56 41 57 48 8d a8 58 fe ff ff 48 81 ec 70 02 00 00 0f 29 70 b8 48 8b fa 48 8b d9 33 f6 89 b5 b0 01 00 00 48 8b 05 ?? ?? ?? ??";
    const char* favorAOB = "41 54 41 55 41 56 41 57 48 8d a8 68 fe ff ff 48 81 ec 60 02 00 00 0f 29 70 b8 0f 29 78 a8 41 8b f1 49 8b f8";
    const char* emblemAOB = "41 54 41 55 41 56 41 57 48 8d ?? ?? ?? 48 81 ec f0 00 00 00 4c 8b e2 4c 8b f1 48 8b 1d 67 8a c7 02 48 89 5d 67";
    const char* lootboxAOB = "48 8d a8 e8 fb ff ff 48 81 ec d8 04 00 00 0f 29 70 a8 0f 29 78 98 44 0f 29 40 88 44 0f 29 88 78 ff ff ff 44 0f 29 90 68 ff ff ff 44 0f 29 98 58 ff ff ff 41 8b f9";
    const char* lootAOB = "48 8d ac 24 d0 e8 ff ff b8 30 18 00 00 e8 ?? ?? ?? ?? 48 2b e0 0f 29 b4 24 20 18 00 00 0f 29 bc 24 10 18 00 00 44 0f 29 84 24 00 18 00 00";
    const char* createMiscAOB = "48 8d 6c 24 d1 48 81 ec f0 00 00 00 45 8b e1 4d 8b f8 48 8b fa 48 8b f1 48 8b 1d ?? ?? ?? ?? 48 89 5d 5f 48 8d 05 66 7d dd 06";
    const char* materialKeyAOB = "48 8d 6c 24 c9 48 81 ec f0 00 00 00 4c 8b e2 4c 8b f1 48 8b 1d ?? ?? ?? ?? 48 89 5d 67 48 8d 05 9c d2 b0 01";
    const char* createMaterialAOB = "48 8d 6c 24 d1 48 81 ec f0 00 00 00 45 8b e1 4d 8b f8 48 8b fa 48 8b f1 48 8b 1d ?? ?? ?? ?? 48 89 5d 5f 48 8d 05 4e 81 dd 06";
    const char* getLevelAOB = "48 8d 68 98 48 81 ec 30 01 00 00 0f 29 70 b8 0f 29 78 a8 44 0f 29 40 98 4d 8b f8 4c 8b ea 4c 8b e1 48 8b 1d 8e 3d 89 03";
    const char* luckCapAOB = "ba 64 00 00 00 e8 22 8d a9 f9";
    const char* nsRare1AOB = "F2 44 0F 11 8D F8 04 00 00 41 B1 01 F2 0F 10 15 ?? ?? ?? ?? 48 8D 95 F8 04 00 00";
    const char* nsRare2AOB = "F2 44 0F 11 8D D8 05 00 00 41 B1 01 F2 0F 10 15 ?? ?? ?? ?? 48 8D 95 D8 05 00 00";
    const char* netherStoneAOB = "48 8d a8 d8 f8 ff ff 48 81 ec f0 07 00 00 0f 29 70 b8 0f 29 78 a8 44 0f 29 40 98 44 0f 29 48 88 44 0f 29 90 78 ff ff ff";
    const char* scrRollAOB = "48 8d 6c 24 90 48 81 ec 70 01 00 00 0f 29 70 b8 0f 29 78 a8 44 0f 29 40 98 41 8b f9 4d 8b e0 4c 8b f9 48 8b 1d 45 3f 38 03";
    const char* creatureMaxBase0AOB = "44 89 64 24 6c f2 0f 10 05 ?? ?? ?? ?? f2 0f 11 44 24 60 c7 45 90 11 00 00 00";
    const char* creatureMaxBase1AOB = "44 89 64 24 6c f2 0f 10 05 ?? ?? ?? ?? f2 0f 11 44 24 60 c7 45 90 18 00 00 00";
    const char* creatureMaxBase2AOB = "44 89 64 24 6c f2 0f 10 05 ?? ?? ?? ?? f2 0f 11 44 24 60 c7 45 90 1f 00 00 00";
    const char* creatureMaxBase3AOB = "44 89 64 24 6c f2 0f 10 05 ?? ?? ?? ?? f2 0f 11 44 24 60 c7 45 90 26 00 00 00";
    const char* creatureMaxBase4AOB = "44 89 64 24 6c f2 0f 10 05 ?? ?? ?? ?? f2 0f 11 44 24 60 c7 45 90 2d 00 00 00";
    const char* fuseJcc1AOB = "83 e1 1f 41 8b c6 d3 e0 a8 46 ?? ?? 48 8d 4d 10 e8 9a 7c 82 f9 90 40 84 ff";
    const char* fuseJcc2AOB = "83 e1 1f 41 8b c6 d3 e0 a8 46 ?? ?? 48 8d 4d 60 e8 8e 76 82 f9 90 40 84 ff";
    const char* talismanMaxRankAOB = "48 8b ec 48 83 ec 70 49 8b f8 48 8b 1d 17 b7 c2 07 48 89 5d 40 48 8d 05 ec ed d1 06";

    // 扫描
    uintptr_t fRes = api->FindPattern(resAOB);
    uintptr_t fFavor = api->FindPattern(favorAOB);
    uintptr_t fEmblem = api->FindPattern(emblemAOB);
    uintptr_t fLootbox = api->FindPattern(lootboxAOB);
    uintptr_t fLoot = api->FindPattern(lootAOB);
    uintptr_t fLevel = api->FindPattern(getLevelAOB);
    uintptr_t fCreateMisc = api->FindPattern(createMiscAOB);
    uintptr_t fMaterialKey = api->FindPattern(materialKeyAOB);
    uintptr_t fCreateMaterial = api->FindPattern(createMaterialAOB);
    uintptr_t fLuckCap = api->FindPattern(luckCapAOB);
    uintptr_t fNsRare1 = api->FindPattern(nsRare1AOB);
    uintptr_t fNsRare2 = api->FindPattern(nsRare2AOB);
    uintptr_t fNetherStone = api->FindPattern(netherStoneAOB);
    uintptr_t fScrRoll = api->FindPattern(scrRollAOB);
    uintptr_t fCMB0 = api->FindPattern(creatureMaxBase0AOB);
    uintptr_t fCMB1 = api->FindPattern(creatureMaxBase1AOB);
    uintptr_t fCMB2 = api->FindPattern(creatureMaxBase2AOB);
    uintptr_t fCMB3 = api->FindPattern(creatureMaxBase3AOB);
    uintptr_t fCMB4 = api->FindPattern(creatureMaxBase4AOB);
    uintptr_t fFuseJcc1 = api->FindPattern(fuseJcc1AOB);
    uintptr_t fFuseJcc2 = api->FindPattern(fuseJcc2AOB);
    uintptr_t fTalismanMaxRank = api->FindPattern(talismanMaxRankAOB);

    // 直接指针
    pReadVarById = (Fn_ReadVarById)AddrFromImageVa(kFUN_1478bbd70);
    api->Log(pReadVarById ? "Direct pointer resolved: FUN_1478bbd70" : "Failed to resolve direct pointer: FUN_1478bbd70");

    // ── 如果 AOB 扫描失败，回退到 ImageVA 直接定位 ───────────────
    if (!fTalismanMaxRank){
        fTalismanMaxRank = AddrFromImageVa(0x141dbf690ULL);
        api->Log("TalismanMaxRank: AOB miss, falling back to ImageVA 0x141dbf690");
    }
    else
    {
        api->Log("TalismanMaxRank: AOB scan hit");
    }

    if (fTalismanMaxRank){
        MH_STATUS st = MH_CreateHook((LPVOID)(fTalismanMaxRank - 16),&HookedTalismanMaxRank,(LPVOID*)&pOriginalTalismanMaxRank);

        if (st == MH_OK)
            api->Log("TalismanMaxRank hook installed: max rank x2 (rank>1)");
        else
        {
            char buf[128];
            sprintf_s(buf, "TalismanMaxRank hook FAILED: MH_STATUS=%d", (int)st);
            api->Log(buf);
        }
    }
    else
    {
        api->Log("TalismanMaxRank: address not found, hook skipped");
    }

	//战斗资源赋值help
    uintptr_t fAssign410 = AddrFromImageVa(kFUN_14028c410);
    uintptr_t fAssign630 = AddrFromImageVa(kFUN_14028c630);

    if (fAssign410 && fAssign630)
    {
        MH_CreateHook((LPVOID)fAssign410, &HookedAssign410, (LPVOID*)&pOriginalAssign410);
        MH_CreateHook((LPVOID)fAssign630, &HookedAssign630, (LPVOID*)&pOriginalAssign630);
        if (g_api)
        {
            char buf[128];
            sprintf_s(buf, "RewardResources Assign hook successfully installed.");
            g_api->Log(buf);
        }
    }

    // ── 主要Hooks ────────────────────────────────────────────
    if (fRes && fFavor && fEmblem && fLootbox && fLevel && fLoot)
    {
        MH_CreateHook((LPVOID)(fRes - 18), &HookedGetRewardResources, (LPVOID*)&pOriginalResources);
        MH_CreateHook((LPVOID)(fFavor - 18), &HookedGodAddFavor, (LPVOID*)&pOriginalFavor); 
        MH_CreateHook((LPVOID)(fEmblem - 16), &HookedEmblemKeyPress, (LPVOID*)&pOriginalEmblemKeyPress);
        MH_CreateHook((LPVOID)(fLootbox - 27), &HookedLootBox, (LPVOID*)&pOriginalLootBox);
        MH_CreateHook((LPVOID)(fLoot - 21), &HookedInvLoot, (LPVOID*)&pOriginalInvLoot);
        MH_CreateHook((LPVOID)(fCreateMisc - 24), &HookedCreateMisc, (LPVOID*)&pOriginalCreateMisc);
        MH_CreateHook((LPVOID)(fCreateMaterial - 24), &HookedCreateMaterial, (LPVOID*)&pOriginalCreateMaterial);
        MH_CreateHook((LPVOID)(fMaterialKey - 24), &HookedMaterialKeyPress, (LPVOID*)&pOriginalMaterialKeyPress);
        pOriginalGetLevel = (GML_Script_Fn)(fLevel - 18);
        MH_EnableHook(MH_ALL_HOOKS);
        api->Log("Ultimate Multiplier Hack: Activated.");
    }
    else api->Log("AOB Scan failed. Mod partially or fully disabled.");

    // ── 幸运上限 ─────────────────────────────────────────────
    if (fLuckCap){
        DWORD old;
        VirtualProtect((LPVOID)(fLuckCap + 1), 4, PAGE_EXECUTE_READWRITE, &old);
        *(int*)(fLuckCap + 1) = 500;
        VirtualProtect((LPVOID)(fLuckCap + 1), 4, old, &old);
        api->Log("Luck cap patched: 100 -> 500");
    }
    else api->Log("Failed to find luck cap. Patch skipped.");

    // ── NetherStone 附加上限 ──────────────────────────────────
    if (fNsRare1) { PatchNetherStoneLimit(fNsRare1, 0x4F8, 0x4014000000000000ULL) ? api->Log("NetherStone rare affix cap patched: 3 -> 5") : api->Log("Failed to patch NetherStone rare affix cap."); }
    else api->Log("Failed to find NetherStone rare affix cap pattern.");

    if (fNsRare2) { PatchNetherStoneLimit(fNsRare2, 0x5D8, 0x4014000000000000ULL) ? api->Log("NetherStone special affix cap patched: 3 -> 5") : api->Log("Failed to patch NetherStone special affix cap."); }
    else api->Log("Failed to find NetherStone special affix cap pattern.");

    // ── NetherStoneCreate + ScrRoll ───────────────────────────
    if (fNetherStone && fScrRoll){
        MH_CreateHook((LPVOID)(fNetherStone - 30), &HookedNetherStoneCreate, (LPVOID*)&pOriginalNetherStoneCreate);
        MH_CreateHook((LPVOID)(fScrRoll - 26), &HookedScrRoll, (LPVOID*)&pOriginalScrRoll);
        MH_EnableHook(MH_ALL_HOOKS);
        api->Log("NetherStoneCreate hook installed.");
    }
    else api->Log("Failed to find NetherStoneCreate pattern.");

    // ── 生物基础倍率 ──────────────────────────────────────────
    {
        const uint64_t k50 = 0x4049000000000000ULL;
        int n = 0;
        if (fCMB0 && PatchSetRspDouble(fCMB0 + 5, 0x60, k50)) n++;
        if (fCMB1 && PatchSetRspDouble(fCMB1 + 5, 0x60, k50)) n++;
        if (fCMB2 && PatchSetRspDouble(fCMB2 + 5, 0x60, k50)) n++;
        if (fCMB3 && PatchSetRspDouble(fCMB3 + 5, 0x60, k50)) n++;
        if (fCMB4 && PatchSetRspDouble(fCMB4 + 5, 0x60, k50)) n++;
        char buf[64]; sprintf_s(buf, "Creature maximum stat base multiplier patched: %d ->50.0", n);
        api->Log(buf);
    }

    // ── 融合重用过滤 ──────────────────────────────────────────
    {
        int n = 0;
        if (fFuseJcc1 && PatchJccRel32ToFallthrough(fFuseJcc1 + 25)) { n++; api->Log("Fuse reuse filter patch #1 applied."); }
        else api->Log("Fuse reuse filter patch #1 failed/not found.");
        if (fFuseJcc2 && PatchJccRel32ToFallthrough(fFuseJcc2 + 25)) { n++; api->Log("Fuse reuse filter patch #2 applied."); }
        else api->Log("Fuse reuse filter patch #2 failed/not found.");
        char buf[64]; sprintf_s(buf, "Fuse reuse filter patches applied: %d/2", n);
        api->Log(buf);
    }
}

BOOL APIENTRY DllMain(HMODULE, DWORD, LPVOID) { return TRUE; }
