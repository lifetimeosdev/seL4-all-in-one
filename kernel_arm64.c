#define CONFIG_ARM_HIKEY_OUTSTANDING_PREFETCHERS 0
#define CONFIG_ARM_HIKEY_PREFETCHER_STRIDE	 0
#define CONFIG_ARM_HIKEY_PREFETCHER_NPFSTRM	 0
#define CONFIG_ARCH_AARCH64			 1 /* KernelSel4ArchAarch64=ON */
#define CONFIG_SEL4_ARCH			 aarch64
#define CONFIG_ARCH_ARM				 1 /* KernelArchARM=ON */
#define CONFIG_ARCH				 arm
#define CONFIG_WORD_SIZE			 64
#define CONFIG_ARM_PLAT				 qemu - arm - virt
#define CONFIG_USER_TOP				 0xa0000000
#define CONFIG_PLAT_QEMU_ARM_VIRT		 1 /* KernelPlatformQEMUArmVirt=ON */
#define CONFIG_PLAT_QEMU_ARM_VIRT		 1 /* KernelPlatformQEMUArmVirt=ON */
#define CONFIG_PLAT				 qemu - arm - virt
#define CONFIG_ARM_CORTEX_A53			 1 /* KernelArmCortexA53=ON */
#define CONFIG_ARCH_ARM_V8A			 1 /* KernelArchArmV8a=ON */
#define CONFIG_ARM_MACH				   /* empty */
#define CONFIG_ARM_PA_SIZE_BITS_40		 1 /* KernelArmPASizeBits40=ON */
#define CONFIG_ARM_ICACHE_VIPT			 1 /* KernelArmICacheVIPT=ON */
#define CONFIG_ARM_HYPERVISOR_SUPPORT		 1 /* KernelArmHypervisorSupport=ON */
#define CONFIG_L1_CACHE_LINE_SIZE_BITS		 6
#define CONFIG_VTIMER_UPDATE_VOFFSET		 1 /* KernelArmVtimerUpdateVOffset=ON */
#define CONFIG_HAVE_FPU				 1 /* KernelHaveFPU=ON */
#define CONFIG_PADDR_USER_DEVICE_TOP		 0x10000000000
#define CONFIG_ROOT_CNODE_SIZE_BITS		 13
#define CONFIG_TIMER_TICK_MS			 2
#define CONFIG_TIME_SLICE			 5
#define CONFIG_RETYPE_FAN_OUT_LIMIT		 256
#define CONFIG_MAX_NUM_WORK_UNITS_PER_PREEMPTION 100
#define CONFIG_RESET_CHUNK_BITS			 8
#define CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS	 230
#define CONFIG_FASTPATH				 1 /* KernelFastpath=ON */
#define CONFIG_NUM_DOMAINS			 1
#define CONFIG_NUM_PRIORITIES			 256
#define CONFIG_MAX_NUM_NODES			 1
#define CONFIG_KERNEL_STACK_BITS		 12
#define CONFIG_FPU_MAX_RESTORES_SINCE_SWITCH	 64
#define CONFIG_DEBUG_BUILD			 1 /* KernelDebugBuild=ON */
#define CONFIG_PRINTING				 1 /* KernelPrinting=ON */
#define CONFIG_NO_BENCHMARKS			 1 /* KernelBenchmarksNone=ON */
#define CONFIG_KERNEL_BENCHMARK			 none
#define CONFIG_MAX_NUM_TRACE_POINTS		 0
#define CONFIG_IRQ_REPORTING			 1 /* KernelIRQReporting=ON */
#define CONFIG_COLOUR_PRINTING			 1 /* KernelColourPrinting=ON */
#define CONFIG_USER_STACK_TRACE_LENGTH		 16
#define CONFIG_KERNEL_OPT_LEVEL_O2		 1 /* KernelOptimisationO2=ON */
#define CONFIG_KERNEL_OPT_LEVEL			 -O2

#define NULL	  ((void *)0)
#define PPTR_BASE (0xffffff8000000000ul)
#define PPTR_TOP  (0xffffffffc0000000ul)

/* This is a page table mapping at the end of the virtual address space
 * to map objects with 4KiB pages rather than 4MiB large pages. */
#define KERNEL_PT_BASE (0xffffffffffe00000ul)

/* The first physical address to map into the kernel's physical memory
 * window */
#define PADDR_BASE (0x0ul)

/* The offset from a physical address to a virtual address in the
 * physical memory window. */
#define PPTR_BASE_OFFSET (PPTR_BASE - PADDR_BASE)

#define physBase 0x40000000

/* The physical memory address to use for mapping the kernel ELF */
#define KERNEL_ELF_PADDR_BASE physBase

/* The base address in virtual memory to use for the kernel ELF mapping */
#define KERNEL_ELF_BASE (PPTR_BASE_OFFSET + KERNEL_ELF_PADDR_BASE)

/* The kernel base offset is a way to translate the kernel image segment
 * from virtual to physical. This translation must be a single offset
 * for for the entire segment (i.e. the kernel image must be contiguous
 * both virtually and physically) */
#define KERNEL_ELF_BASE_OFFSET (KERNEL_ELF_BASE - KERNEL_ELF_PADDR_BASE)

/* The base address in virtual memory to use for the kernel device
 * mapping region. These are mapped in the kernel page table. */
#define KDEV_BASE KERNEL_PT_BASE

#define UART_PPTR		(KDEV_BASE + 0x0)
#define GIC_V2_DISTRIBUTOR_PPTR (KDEV_BASE + 0x1000)
#define GIC_V2_CONTROLLER_PPTR	(KDEV_BASE + 0x2000)

#define seL4_PageBits	   12
#define seL4_LargePageBits 21
#define seL4_HugePageBits  30

#define seL4_PageTableBits	12
#define seL4_PageTableEntryBits 3
#define seL4_PageTableIndexBits 9

#define seL4_PageDirBits      12
#define seL4_PageDirEntryBits 3
#define seL4_PageDirIndexBits 9

#define PDE_SIZE_BITS seL4_PageDirEntryBits
#define PD_INDEX_BITS seL4_PageDirIndexBits
#define PTE_SIZE_BITS seL4_PageTableEntryBits
#define PT_INDEX_BITS seL4_PageTableIndexBits

#define PGD_SIZE_BITS  12
#define PGD_INDEX_BITS 9
#define PUD_SIZE_BITS  12
#define PUD_INDEX_BITS 9

#define PT_INDEX_OFFSET	 (seL4_PageBits)
#define PD_INDEX_OFFSET	 (PT_INDEX_OFFSET + PT_INDEX_BITS)
#define PUD_INDEX_OFFSET (PD_INDEX_OFFSET + PD_INDEX_BITS)
#define PGD_INDEX_OFFSET (PUD_INDEX_OFFSET + PUD_INDEX_BITS)

#define BIT(n)		 (1ul << (n))
#define MASK(n)		 (BIT(n) - 1ul)
#define ROUND_DOWN(n, b) (((n) >> (b)) << (b))
#define ROUND_UP(n, b)	 (((((n)-1ul) >> (b)) + 1ul) << (b))

typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;
typedef signed char int8_t;
typedef signed short int16_t;
typedef signed int int32_t;
typedef signed long long int64_t;
typedef uint64_t uintmax_t;
typedef int64_t intmax_t;
/* There is no difference between using 'ul' or 'lu' as suffix for numbers to
 * enforce a specific type besides the default 'int'. Just when it comes to the
 * printf() format specifiers, '%lu' is the only form that is supported. Thus
 * 'ul' is the preferred suffix to avoid confusion.
 */
/* Time constants are defined to use the 'unsigned long long'. Rationale is,
 * that the C rules define the calculation result is determined by largest type
 * involved. Enforcing the largest possible type C provides avoids pitfalls with
 * 32-bit overflows when values are getting quite large. Keep in mind that even
 * 2^32 milli-seconds roll over within 50 days, which is an uptime that embedded
 * systems will reach easily and it resembles not even two months in a calendar
 * calculation. In addition, using the largest integer type C currently defines
 * enforces that all calculations results need a cast back to a 32-bit type
 * explicitly. This might feel annoying, but practically it makes code more
 * robust and enforces thinking about potential overflows.
 * Note that at this stage of the includes, we do not have defined the type
 * uint64_t yet, so we can't use any definitions around it, but have to stick to
 * plain C types. Neither moving the time constant definitions behind the
 * uint64_t type definitions nor including the header with the uint64_t
 * definitions here is currently a feasible option.
 */
/** MODIFIES: */
void __builtin_unreachable(void);
/* Borrowed from linux/include/linux/compiler.h */
/* need that for compiling with c99 instead of gnu99 */
/* Evaluate a Kconfig-provided configuration setting at compile-time. */
/* Check the existence of a configuration setting, returning one value if it
 * exists and a different one if it does not */
/** MODIFIES:
    FNSPEC
	halt_spec: "\<Gamma> \<turnstile> {} Call halt_'proc {}"
*/
void halt(void);
void memzero(void *s, unsigned long n);
void *memset(void *s, unsigned long c, unsigned long n);
void *memcpy(void *ptr_dst, const void *ptr_src, unsigned long n);
int strncmp(const char *s1, const char *s2, int n);
long char_to_long(char c);
long str_to_long(const char *str);
/* Library functions for counting leading/trailing zeros.
 *
 * GCC/LLVM provides builtin function like __builtin_clzl() for this, which
 * either get translated to machine specific instructions or calls helper
 * functions like __clzsi2() that a compiler library is expected to implement.
 * At the time of writing this comment, the GCC documentation about the compiler
 * library (https://gcc.gnu.org/onlinedocs/gccint/Integer-library-routines.html)
 * is not very detailed and the signatures given for these helper functions
 * appear incorrect. For example, is says "int __clzsi2(unsigned int a)", but
 * both the GCC and LLVM libraries implement it in a way that is independent of
 * the implementation choices for the sizes of `unsigned int`. Instead, it
 * appears that `si` always signifies a 32-bit argument and `di` always
 * signifies a 64-bit argument. Tests with __builtin_clzl() on RISC-V have shown
 * that if 'unsigned long' is 32 bits __builtin_clzl() uses __clzsi2() and if
 * the type is 64 bits __builtin_clzl() uses __clzdi2(). Thus using the types
 * uint32_t and uint64_t from stdint.h in the signatures below is considered the
 * semantically correct way.
 * Note that we only emit actual function implementations for these functions if
 * CONFIG_CLZ_32 etc. are set. Otherwise, the compiler's internal implementation
 * may get used or compilation fails if there is no machine instruction.
 */
int __clzsi2(uint32_t x);
int __clzdi2(uint64_t x);
int __ctzsi2(uint32_t x);
int __ctzdi2(uint64_t x);
// Used for compile-time constants, so should always use the builtin.
// Count leading zeros.
// The CONFIG_CLZ_NO_BUILTIN macro may be used to expose the library function
// to the C parser for verification.
// If we use a compiler builtin, we cannot verify it, so we use the following
// annotations to hide the function body from the proofs, and axiomatise its
// behaviour.
// On the other hand, if we use our own implementation instead of the builtin,
// then we want to expose that implementation to the proofs, and therefore hide
// these annotations.
/** MODIFIES: */
/** DONT_TRANSLATE */
/** FNSPEC clzl_spec:
  "\<forall>s. \<Gamma> \<turnstile>
    {\<sigma>. s = \<sigma> \<and> x___unsigned_long_' s \<noteq> 0 }
      \<acute>ret__long :== PROC clzl(\<acute>x)
    \<lbrace> \<acute>ret__long = of_nat (word_clz (x___unsigned_long_' s)) \<rbrace>"
*/
static inline long clzl(unsigned long x)
{
	return __builtin_clzl(x);
}
// See comments on clzl.
/** MODIFIES: */
/** DONT_TRANSLATE */
/** FNSPEC clzll_spec:
  "\<forall>s. \<Gamma> \<turnstile>
    {\<sigma>. s = \<sigma> \<and> x___unsigned_longlong_' s \<noteq> 0 }
      \<acute>ret__longlong :== PROC clzll(\<acute>x)
    \<lbrace> \<acute>ret__longlong = of_nat (word_clz (x___unsigned_longlong_' s)) \<rbrace>"
*/
static inline long long clzll(unsigned long long x)
{
	return __builtin_clzll(x);
}
// Count trailing zeros.
// See comments on clzl.
/** MODIFIES: */
/** DONT_TRANSLATE */
/** FNSPEC ctzl_spec:
  "\<forall>s. \<Gamma> \<turnstile>
    {\<sigma>. s = \<sigma> \<and> x___unsigned_long_' s \<noteq> 0 }
      \<acute>ret__long :== PROC ctzl(\<acute>x)
    \<lbrace> \<acute>ret__long = of_nat (word_ctz (x___unsigned_long_' s)) \<rbrace>"
*/
static inline long ctzl(unsigned long x)
{
	// Here, we have __builtin_ctzl.
	return __builtin_ctzl(x);
}
// See comments on clzl.
/** MODIFIES: */
/** DONT_TRANSLATE */
/** FNSPEC ctzll_spec:
  "\<forall>s. \<Gamma> \<turnstile>
    {\<sigma>. s = \<sigma> \<and> x___unsigned_longlong_' s \<noteq> 0 }
      \<acute>ret__longlong :== PROC ctzll(\<acute>x)
    \<lbrace> \<acute>ret__longlong = of_nat (word_ctz (x___unsigned_longlong_' s)) \<rbrace>"
*/
static inline long long ctzll(unsigned long long x)
{
	return __builtin_ctzll(x);
}
int __builtin_popcountl(unsigned long x);
/** DONT_TRANSLATE */
static inline long popcountl(unsigned long mask)
{
	unsigned int count; // c accumulates the total bits set in v
	for (count = 0; mask; count++) {
		mask &= mask - 1; // clear the least significant bit set
	}
	return count;
}
/* Can be used to insert padding to the next L1 cache line boundary */
void _fail(const char *str, const char *file, unsigned int line, const char *function);
/* Create an assert that triggers a compile error if the condition fails. We do
 * not include sel4/macros.h that provides SEL4_COMPILE_ASSERT() for two
 * reasons:
 * - The kernel's source internals shall not have any unnecessary dependency on
 *     the user interface headers.
 * - The kernel user API headers aims to be compiler agnostic and stick to the
 *     standard(s). As _Static_assert() is a c11 feature, the c99 used for
 *     kernel compilation would use a helper macro. While this works, it
 *     creates strange error messages when the condition fails. Since kernel
 *     compilation supports just gcc and clang, and both are known to provide
 *     _Static_assert() even in c99, we can just use this.
 *
 * Unfortunately, the C parser does not understand _Static_assert(), so there is
 * still the need for the helper macro there. In addition, the macro
 * unverified_compile_assert() exists, because some compile asserts contain
 * expressions that the C parser cannot handle, too.
 */
_Static_assert(sizeof(unsigned long) == 8, "long_is_64bits");
typedef uint64_t timestamp_t;
typedef unsigned long word_t;
typedef signed long sword_t;
/* for printf() formatting */
typedef word_t vptr_t;
typedef word_t paddr_t;
typedef word_t pptr_t;
typedef word_t cptr_t;
typedef word_t node_id_t;
typedef word_t cpu_id_t;
typedef word_t dom_t;
typedef uint8_t hw_asid_t;
enum hwASIDConstants { hwASIDMax = 255, hwASIDBits = 8 };
typedef struct kernel_frame {
	paddr_t paddr;
	pptr_t pptr;
	int armExecuteNever;
	int userAvailable;
} kernel_frame_t;
/* arch/types.h is supposed to define word_t and _seL4_word_fmt */
/* Using multiple macro layers may look strange, but this is required to make
 * the preprocessor fully evaluate all macro parameters first and then pass the
 * result as parameter to the next macro layer. This allows passing macros as
 * parameters also, and not just plain strings. The final concatenation will
 * always be from the strings behind all macros then - and not the macro names
 * that are passed as parameters.
 */
/* The C parser from the verification toolchain requires declaring word_t
 * constants without casting integer values to word_t. Since the printf() format
 * specifiers are aligned with the C integer type suffixes, _seL4_word_fmt can
 * be used there also.
 */
enum _bool { false = 0, true = 1 };
typedef word_t bool_t;
typedef struct region {
	pptr_t start;
	pptr_t end;
} region_t;
typedef struct p_region {
	paddr_t start;
	paddr_t end;
} p_region_t;
typedef struct v_region {
	vptr_t start;
	vptr_t end;
} v_region_t;
/* for libsel4 headers that the kernel shares */
typedef uint8_t seL4_Uint8;
typedef uint16_t seL4_Uint16;
typedef uint32_t seL4_Uint32;
typedef word_t seL4_Word;
typedef cptr_t seL4_CPtr;
typedef node_id_t seL4_NodeId;
typedef paddr_t seL4_PAddr;
typedef dom_t seL4_Domain;
struct seL4_CNode_CapData {
	uint64_t words[1];
};
typedef struct seL4_CNode_CapData seL4_CNode_CapData_t;
static inline uint64_t seL4_CNode_CapData_get_guard(seL4_CNode_CapData_t seL4_CNode_CapData)
{
	uint64_t ret;
	ret = (seL4_CNode_CapData.words[0] & 0xffffffffffffffc0ull) >> 6;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (63)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t seL4_CNode_CapData_get_guardSize(seL4_CNode_CapData_t seL4_CNode_CapData)
{
	uint64_t ret;
	ret = (seL4_CNode_CapData.words[0] & 0x3full) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (63)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
struct seL4_CapRights {
	uint64_t words[1];
};
typedef struct seL4_CapRights seL4_CapRights_t;
static inline uint64_t seL4_CapRights_get_capAllowGrantReply(seL4_CapRights_t seL4_CapRights)
{
	uint64_t ret;
	ret = (seL4_CapRights.words[0] & 0x8ull) >> 3;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (63)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t seL4_CapRights_get_capAllowGrant(seL4_CapRights_t seL4_CapRights)
{
	uint64_t ret;
	ret = (seL4_CapRights.words[0] & 0x4ull) >> 2;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (63)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t seL4_CapRights_get_capAllowRead(seL4_CapRights_t seL4_CapRights)
{
	uint64_t ret;
	ret = (seL4_CapRights.words[0] & 0x2ull) >> 1;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (63)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t seL4_CapRights_get_capAllowWrite(seL4_CapRights_t seL4_CapRights)
{
	uint64_t ret;
	ret = (seL4_CapRights.words[0] & 0x1ull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (63)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
struct seL4_MessageInfo {
	uint64_t words[1];
};
typedef struct seL4_MessageInfo seL4_MessageInfo_t;
static inline seL4_MessageInfo_t seL4_MessageInfo_new(uint64_t label, uint64_t capsUnwrapped,
						      uint64_t extraCaps, uint64_t length)
{
	seL4_MessageInfo_t seL4_MessageInfo;
	/* fail if user has passed bits that we will override */
	seL4_MessageInfo.words[0] = 0 | (label & 0xfffffffffffffull) << 12 |
				    (capsUnwrapped & 0x7ull) << 9 | (extraCaps & 0x3ull) << 7 |
				    (length & 0x7full) << 0;
	return seL4_MessageInfo;
}
static inline uint64_t seL4_MessageInfo_get_label(seL4_MessageInfo_t seL4_MessageInfo)
{
	uint64_t ret;
	ret = (seL4_MessageInfo.words[0] & 0xfffffffffffff000ull) >> 12;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (63)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t seL4_MessageInfo_get_capsUnwrapped(seL4_MessageInfo_t seL4_MessageInfo)
{
	uint64_t ret;
	ret = (seL4_MessageInfo.words[0] & 0xe00ull) >> 9;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (63)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline seL4_MessageInfo_t
seL4_MessageInfo_set_capsUnwrapped(seL4_MessageInfo_t seL4_MessageInfo, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	seL4_MessageInfo.words[0] &= ~0xe00ull;
	seL4_MessageInfo.words[0] |= (v64 << 9) & 0xe00ull;
	return seL4_MessageInfo;
}
static inline uint64_t seL4_MessageInfo_get_extraCaps(seL4_MessageInfo_t seL4_MessageInfo)
{
	uint64_t ret;
	ret = (seL4_MessageInfo.words[0] & 0x180ull) >> 7;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (63)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline seL4_MessageInfo_t seL4_MessageInfo_set_extraCaps(seL4_MessageInfo_t seL4_MessageInfo,
								uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	seL4_MessageInfo.words[0] &= ~0x180ull;
	seL4_MessageInfo.words[0] |= (v64 << 7) & 0x180ull;
	return seL4_MessageInfo;
}
static inline uint64_t seL4_MessageInfo_get_length(seL4_MessageInfo_t seL4_MessageInfo)
{
	uint64_t ret;
	ret = (seL4_MessageInfo.words[0] & 0x7full) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (63)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline seL4_MessageInfo_t seL4_MessageInfo_set_length(seL4_MessageInfo_t seL4_MessageInfo,
							     uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	seL4_MessageInfo.words[0] &= ~0x7full;
	seL4_MessageInfo.words[0] |= (v64 << 0) & 0x7full;
	return seL4_MessageInfo;
}
typedef enum api_object {
	seL4_UntypedObject,
	seL4_TCBObject,
	seL4_EndpointObject,
	seL4_NotificationObject,
	seL4_CapTableObject,
	seL4_NonArchObjectTypeCount,
} seL4_ObjectType;
typedef seL4_Word api_object_t;
typedef enum _mode_object {
	seL4_ARM_HugePageObject = seL4_NonArchObjectTypeCount,
	seL4_ARM_PageUpperDirectoryObject,
	seL4_ARM_PageGlobalDirectoryObject,
	seL4_ModeObjectTypeCount
} seL4_ModeObjectType;
typedef enum _object {
	seL4_ARM_SmallPageObject = seL4_ModeObjectTypeCount,
	seL4_ARM_LargePageObject,
	seL4_ARM_PageTableObject,
	seL4_ARM_PageDirectoryObject,
	seL4_ObjectTypeCount
} seL4_ArchObjectType;
typedef seL4_Word object_t;
enum asidConstants { asidInvalid = 0 };
typedef word_t asid_t;
/* _Static_assert() is a c11 feature. Since the kernel is currently compiled
 * with c99, we have to emulate it. */
/*
 * Some compilers attempt to pack enums into the smallest possible type.
 * For ABI compatibility with the kernel, we need to ensure they remain
 * the same size as a 'long'.
 */
enum priorityConstants { seL4_InvalidPrio = -1, seL4_MinPrio = 0, seL4_MaxPrio = 256 - 1 };
/* seL4_MessageInfo_t defined in api/shared_types.bf */
enum seL4_MsgLimits { seL4_MsgLengthBits = 7, seL4_MsgExtraCapBits = 2 };
enum {
	seL4_MsgMaxLength = 120,
};
/* seL4_CapRights_t defined in shared_types_*.bf */
typedef enum {
	seL4_NoFailure = 0,
	seL4_InvalidRoot,
	seL4_MissingCapability,
	seL4_DepthMismatch,
	seL4_GuardMismatch,
	_enum_pad_seL4_LookupFailureType = ((1ULL << ((sizeof(long) * 8) - 1)) - 1),
} seL4_LookupFailureType;
/* this file is shared between the kernel and libsel4 */
typedef struct seL4_IPCBuffer_ {
	seL4_MessageInfo_t tag;
	seL4_Word msg[seL4_MsgMaxLength];
	seL4_Word userData;
	seL4_Word caps_or_badges[((1ul << (seL4_MsgExtraCapBits)) - 1)];
	seL4_CPtr receiveCNode;
	seL4_CPtr receiveIndex;
	seL4_Word receiveDepth;
} seL4_IPCBuffer __attribute__((__aligned__(sizeof(struct seL4_IPCBuffer_))));
typedef enum {
	seL4_CapFault_IP,
	seL4_CapFault_Addr,
	seL4_CapFault_InRecvPhase,
	seL4_CapFault_LookupFailureType,
	seL4_CapFault_BitsLeft,
	seL4_CapFault_DepthMismatch_BitsFound,
	seL4_CapFault_GuardMismatch_GuardFound = seL4_CapFault_DepthMismatch_BitsFound,
	seL4_CapFault_GuardMismatch_BitsFound,
	_enum_pad_seL4_CapFault_Msg = ((1ULL << ((sizeof(long) * 8) - 1)) - 1),
} seL4_CapFault_Msg;
/* io for dumping capdl */
unsigned char kernel_getDebugChar(void);
typedef __builtin_va_list va_list;
/* the actual output function */
void kernel_putDebugChar(unsigned char c);
/* This is the actual implementation of the kernel printing API. It must never
 * be called directly from anywhere except the function defined in this file.
 */
int impl_kvprintf(const char *format, va_list ap);
int impl_ksnvprintf(char *str, word_t size, const char *format, va_list ap);
/*
 *------------------------------------------------------------------------------
 * Kernel printing API
 *------------------------------------------------------------------------------
 */
/* Writes a character to the kernel output channel. This is used to implement
 * the syscall SysDebugPutChar.
 */
static inline void kernel_putchar(char c)
{
	/* Write to target specific debug output channel. */
	kernel_putDebugChar(c);
}
/* Writes a character to the active output channel. This is used by all code
 * related to printf(). Contrary to the common signature of putchar(), there is
 * no return value here.
 */
static inline void putchar(char c)
{
	/* Write to target specific debug output channel. Purposely, we do not call
	 * kernel_putchar() here, as the kernel printf() channel is semantically
	 * different from the syscall SysDebugPutChar channel. The unification
	 * of both channels happens at the lower layer eventually
	 */
	kernel_putDebugChar(c);
}
/* Writes the string and a trailing newline. There is no point to enforce a
 * kernel_puts(), as this is just a wrapper for putchar() anyway.
 */
static inline int puts(const char *str)
{
	if (str) {
		while (*str) {
			putchar(*str++);
		}
	}
	putchar('\n');
	/* Standards define that a non-negative number is returned on success. */
	return 0;
}
/* There should only be a kprintf() that all kernel code must use for printing,
 * but for convenience we provide a printf() here.
 */
static inline __attribute__((format(printf, 1, 2))) int printf(const char *format, ...)
{
	va_list args;
	__builtin_va_start(args, format);
	int ret = impl_kvprintf(format, args); /* will call putchar() eventually */
	__builtin_va_end(args);
	return ret;
}
/* Provide the standard snprintf() for write formatted data into a buffer, which
 * can then be printed or stored.
 */
static inline __attribute__((format(printf, 3, 4))) int snprintf(char *buf, word_t size,
								 const char *format, ...)
{
	va_list args;
	__builtin_va_start(args, format);
	int ret = impl_ksnvprintf(buf, size, format, args);
	__builtin_va_end(args);
	return ret;
}
/* seL4_CapRights_t defined in mode/api/shared_types.bf */
typedef word_t prio_t;
typedef uint64_t ticks_t;
typedef uint64_t time_t;
enum domainConstants {
	minDom = 0,
	maxDom = 1 - 1,
	/* To analyse branches of control flow decisions based on the number of
	 * domains without knowing their exact number, verification needs a C name
	 * to relate to higher-level specs. */
	numDomains = 1
};
struct cap_transfer {
	cptr_t ctReceiveRoot;
	cptr_t ctReceiveIndex;
	word_t ctReceiveDepth;
};
typedef struct cap_transfer cap_transfer_t;
enum ctLimits { capTransferDataSize = 3 };
static inline seL4_CapRights_t rightsFromWord(word_t w)
{
	seL4_CapRights_t seL4_CapRights;
	seL4_CapRights.words[0] = w;
	return seL4_CapRights;
}
static inline word_t wordFromRights(seL4_CapRights_t seL4_CapRights)
{
	return seL4_CapRights.words[0] & ((1ul << (4)) - 1ul);
}
static inline cap_transfer_t capTransferFromWords(word_t *wptr)
{
	cap_transfer_t transfer;
	transfer.ctReceiveRoot = (cptr_t)wptr[0];
	transfer.ctReceiveIndex = (cptr_t)wptr[1];
	transfer.ctReceiveDepth = wptr[2];
	return transfer;
}
static inline seL4_MessageInfo_t messageInfoFromWord_raw(word_t w)
{
	seL4_MessageInfo_t mi;
	mi.words[0] = w;
	return mi;
}
static inline seL4_MessageInfo_t messageInfoFromWord(word_t w)
{
	seL4_MessageInfo_t mi;
	word_t len;
	mi.words[0] = w;
	len = seL4_MessageInfo_get_length(mi);
	if (len > seL4_MsgMaxLength) {
		mi = seL4_MessageInfo_set_length(mi, seL4_MsgMaxLength);
	}
	return mi;
}
static inline word_t wordFromMessageInfo(seL4_MessageInfo_t mi)
{
	return mi.words[0];
}
/*
 * thread name is only available if the kernel is built in debug mode.
 */
/*
 * Print to serial a message helping userspace programmers to determine why the
 * kernel is not performing their requested operation.
 */
struct endpoint {
	uint64_t words[2];
};
typedef struct endpoint endpoint_t;
static inline uint64_t endpoint_ptr_get_epQueue_head(endpoint_t *endpoint_ptr)
{
	uint64_t ret;
	ret = (endpoint_ptr->words[1] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void endpoint_ptr_set_epQueue_head(endpoint_t *endpoint_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	endpoint_ptr->words[1] &= ~0xffffffffffffffffull;
	endpoint_ptr->words[1] |= (v64 << 0) & 0xffffffffffffffff;
}
static inline uint64_t endpoint_ptr_get_epQueue_tail(endpoint_t *endpoint_ptr)
{
	uint64_t ret;
	ret = (endpoint_ptr->words[0] & 0xfffffffffffcull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline void endpoint_ptr_set_epQueue_tail(endpoint_t *endpoint_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	endpoint_ptr->words[0] &= ~0xfffffffffffcull;
	endpoint_ptr->words[0] |= (v64 >> 0) & 0xfffffffffffc;
}
static inline uint64_t endpoint_ptr_get_state(endpoint_t *endpoint_ptr)
{
	uint64_t ret;
	ret = (endpoint_ptr->words[0] & 0x3ull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void endpoint_ptr_set_state(endpoint_t *endpoint_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	endpoint_ptr->words[0] &= ~0x3ull;
	endpoint_ptr->words[0] |= (v64 << 0) & 0x3;
}
struct mdb_node {
	uint64_t words[2];
};
typedef struct mdb_node mdb_node_t;
static inline mdb_node_t mdb_node_new(uint64_t mdbNext, uint64_t mdbRevocable,
				      uint64_t mdbFirstBadged, uint64_t mdbPrev)
{
	mdb_node_t mdb_node;
	/* fail if user has passed bits that we will override */
	mdb_node.words[0] = 0 | mdbPrev << 0;
	mdb_node.words[1] = 0 | (mdbNext & 0xfffffffffffcull) >> 0 | (mdbRevocable & 0x1ull) << 1 |
			    (mdbFirstBadged & 0x1ull) << 0;
	return mdb_node;
}
static inline uint64_t mdb_node_get_mdbNext(mdb_node_t mdb_node)
{
	uint64_t ret;
	ret = (mdb_node.words[1] & 0xfffffffffffcull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline void mdb_node_ptr_set_mdbNext(mdb_node_t *mdb_node_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	mdb_node_ptr->words[1] &= ~0xfffffffffffcull;
	mdb_node_ptr->words[1] |= (v64 >> 0) & 0xfffffffffffc;
}
static inline uint64_t mdb_node_get_mdbRevocable(mdb_node_t mdb_node)
{
	uint64_t ret;
	ret = (mdb_node.words[1] & 0x2ull) >> 1;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline mdb_node_t mdb_node_set_mdbRevocable(mdb_node_t mdb_node, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	mdb_node.words[1] &= ~0x2ull;
	mdb_node.words[1] |= (v64 << 1) & 0x2ull;
	return mdb_node;
}
static inline void mdb_node_ptr_set_mdbRevocable(mdb_node_t *mdb_node_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	mdb_node_ptr->words[1] &= ~0x2ull;
	mdb_node_ptr->words[1] |= (v64 << 1) & 0x2;
}
static inline uint64_t mdb_node_get_mdbFirstBadged(mdb_node_t mdb_node)
{
	uint64_t ret;
	ret = (mdb_node.words[1] & 0x1ull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline mdb_node_t mdb_node_set_mdbFirstBadged(mdb_node_t mdb_node, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	mdb_node.words[1] &= ~0x1ull;
	mdb_node.words[1] |= (v64 << 0) & 0x1ull;
	return mdb_node;
}
static inline void mdb_node_ptr_set_mdbFirstBadged(mdb_node_t *mdb_node_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	mdb_node_ptr->words[1] &= ~0x1ull;
	mdb_node_ptr->words[1] |= (v64 << 0) & 0x1;
}
static inline uint64_t mdb_node_get_mdbPrev(mdb_node_t mdb_node)
{
	uint64_t ret;
	ret = (mdb_node.words[0] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline mdb_node_t mdb_node_set_mdbPrev(mdb_node_t mdb_node, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	mdb_node.words[0] &= ~0xffffffffffffffffull;
	mdb_node.words[0] |= (v64 << 0) & 0xffffffffffffffffull;
	return mdb_node;
}
static inline void mdb_node_ptr_set_mdbPrev(mdb_node_t *mdb_node_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	mdb_node_ptr->words[0] &= ~0xffffffffffffffffull;
	mdb_node_ptr->words[0] |= (v64 << 0) & 0xffffffffffffffff;
}
struct notification {
	uint64_t words[4];
};
typedef struct notification notification_t;
static inline uint64_t notification_ptr_get_ntfnBoundTCB(notification_t *notification_ptr)
{
	uint64_t ret;
	ret = (notification_ptr->words[3] & 0xffffffffffffull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline void notification_ptr_set_ntfnBoundTCB(notification_t *notification_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	notification_ptr->words[3] &= ~0xffffffffffffull;
	notification_ptr->words[3] |= (v64 >> 0) & 0xffffffffffff;
}
static inline uint64_t notification_ptr_get_ntfnMsgIdentifier(notification_t *notification_ptr)
{
	uint64_t ret;
	ret = (notification_ptr->words[2] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void notification_ptr_set_ntfnMsgIdentifier(notification_t *notification_ptr,
							  uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	notification_ptr->words[2] &= ~0xffffffffffffffffull;
	notification_ptr->words[2] |= (v64 << 0) & 0xffffffffffffffff;
}
static inline uint64_t notification_ptr_get_ntfnQueue_head(notification_t *notification_ptr)
{
	uint64_t ret;
	ret = (notification_ptr->words[1] & 0xffffffffffffull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline void notification_ptr_set_ntfnQueue_head(notification_t *notification_ptr,
						       uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	notification_ptr->words[1] &= ~0xffffffffffffull;
	notification_ptr->words[1] |= (v64 >> 0) & 0xffffffffffff;
}
static inline uint64_t notification_ptr_get_ntfnQueue_tail(notification_t *notification_ptr)
{
	uint64_t ret;
	ret = (notification_ptr->words[0] & 0xffffffffffff0000ull) >> 16;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline void notification_ptr_set_ntfnQueue_tail(notification_t *notification_ptr,
						       uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	notification_ptr->words[0] &= ~0xffffffffffff0000ull;
	notification_ptr->words[0] |= (v64 << 16) & 0xffffffffffff0000;
}
static inline uint64_t notification_ptr_get_state(notification_t *notification_ptr)
{
	uint64_t ret;
	ret = (notification_ptr->words[0] & 0x3ull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void notification_ptr_set_state(notification_t *notification_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	notification_ptr->words[0] &= ~0x3ull;
	notification_ptr->words[0] |= (v64 << 0) & 0x3;
}
struct pte {
	uint64_t words[1];
};
typedef struct pte pte_t;
static inline pte_t pte_new(uint64_t UXN, uint64_t page_base_address, uint64_t nG, uint64_t AF,
			    uint64_t SH, uint64_t AP, uint64_t AttrIndx, uint64_t reserved)
{
	pte_t pte;
	/* fail if user has passed bits that we will override */
	pte.words[0] = 0 | (UXN & 0x1ull) << 54 | (page_base_address & 0xfffffffff000ull) >> 0 |
		       (nG & 0x1ull) << 11 | (AF & 0x1ull) << 10 | (SH & 0x3ull) << 8 |
		       (AP & 0x3ull) << 6 | (AttrIndx & 0x7ull) << 2 | (reserved & 0x3ull) << 0;
	return pte;
}
static inline uint64_t pte_ptr_get_UXN(pte_t *pte_ptr)
{
	uint64_t ret;
	ret = (pte_ptr->words[0] & 0x40000000000000ull) >> 54;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t pte_ptr_get_page_base_address(pte_t *pte_ptr)
{
	uint64_t ret;
	ret = (pte_ptr->words[0] & 0xfffffffff000ull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t pte_ptr_get_SH(pte_t *pte_ptr)
{
	uint64_t ret;
	ret = (pte_ptr->words[0] & 0x300ull) >> 8;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t pte_ptr_get_AP(pte_t *pte_ptr)
{
	uint64_t ret;
	ret = (pte_ptr->words[0] & 0xc0ull) >> 6;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t pte_ptr_get_reserved(pte_t *pte_ptr)
{
	uint64_t ret;
	ret = (pte_ptr->words[0] & 0x3ull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
struct thread_state {
	uint64_t words[3];
};
typedef struct thread_state thread_state_t;
static inline uint64_t thread_state_ptr_get_blockingIPCBadge(thread_state_t *thread_state_ptr)
{
	uint64_t ret;
	ret = (thread_state_ptr->words[2] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void thread_state_ptr_set_blockingIPCBadge(thread_state_t *thread_state_ptr,
							 uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	thread_state_ptr->words[2] &= ~0xffffffffffffffffull;
	thread_state_ptr->words[2] |= (v64 << 0) & 0xffffffffffffffff;
}
static inline uint64_t thread_state_ptr_get_blockingIPCCanGrant(thread_state_t *thread_state_ptr)
{
	uint64_t ret;
	ret = (thread_state_ptr->words[1] & 0x8ull) >> 3;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void thread_state_ptr_set_blockingIPCCanGrant(thread_state_t *thread_state_ptr,
							    uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	thread_state_ptr->words[1] &= ~0x8ull;
	thread_state_ptr->words[1] |= (v64 << 3) & 0x8;
}
static inline uint64_t
thread_state_ptr_get_blockingIPCCanGrantReply(thread_state_t *thread_state_ptr)
{
	uint64_t ret;
	ret = (thread_state_ptr->words[1] & 0x4ull) >> 2;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void thread_state_ptr_set_blockingIPCCanGrantReply(thread_state_t *thread_state_ptr,
								 uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	thread_state_ptr->words[1] &= ~0x4ull;
	thread_state_ptr->words[1] |= (v64 << 2) & 0x4;
}
static inline uint64_t thread_state_ptr_get_blockingIPCIsCall(thread_state_t *thread_state_ptr)
{
	uint64_t ret;
	ret = (thread_state_ptr->words[1] & 0x2ull) >> 1;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void thread_state_ptr_set_blockingIPCIsCall(thread_state_t *thread_state_ptr,
							  uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	thread_state_ptr->words[1] &= ~0x2ull;
	thread_state_ptr->words[1] |= (v64 << 1) & 0x2;
}
static inline uint64_t thread_state_get_tcbQueued(thread_state_t thread_state)
{
	uint64_t ret;
	ret = (thread_state.words[1] & 0x1ull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void thread_state_ptr_set_tcbQueued(thread_state_t *thread_state_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	thread_state_ptr->words[1] &= ~0x1ull;
	thread_state_ptr->words[1] |= (v64 << 0) & 0x1;
}
static inline uint64_t thread_state_ptr_get_blockingObject(thread_state_t *thread_state_ptr)
{
	uint64_t ret;
	ret = (thread_state_ptr->words[0] & 0xfffffffffff0ull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline void thread_state_ptr_set_blockingObject(thread_state_t *thread_state_ptr,
						       uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	thread_state_ptr->words[0] &= ~0xfffffffffff0ull;
	thread_state_ptr->words[0] |= (v64 >> 0) & 0xfffffffffff0;
}
static inline uint64_t thread_state_get_tsType(thread_state_t thread_state)
{
	uint64_t ret;
	ret = (thread_state.words[0] & 0xfull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t thread_state_ptr_get_tsType(thread_state_t *thread_state_ptr)
{
	uint64_t ret;
	ret = (thread_state_ptr->words[0] & 0xfull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void thread_state_ptr_set_tsType(thread_state_t *thread_state_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	thread_state_ptr->words[0] &= ~0xfull;
	thread_state_ptr->words[0] |= (v64 << 0) & 0xf;
}
struct ttbr {
	uint64_t words[1];
};
typedef struct ttbr ttbr_t;
static inline ttbr_t ttbr_new(uint64_t asid, uint64_t base_address)
{
	ttbr_t ttbr;
	/* fail if user has passed bits that we will override */
	ttbr.words[0] = 0 | (asid & 0xffffull) << 48 | (base_address & 0xffffffffffffull) >> 0;
	return ttbr;
}
struct vm_attributes {
	uint64_t words[1];
};
typedef struct vm_attributes vm_attributes_t;
static inline vm_attributes_t vm_attributes_new(uint64_t armExecuteNever, uint64_t armParityEnabled,
						uint64_t armPageCacheable)
{
	vm_attributes_t vm_attributes;
	/* fail if user has passed bits that we will override */
	vm_attributes.words[0] = 0 | (armExecuteNever & 0x1ull) << 2 |
				 (armParityEnabled & 0x1ull) << 1 |
				 (armPageCacheable & 0x1ull) << 0;
	return vm_attributes;
}
static inline uint64_t vm_attributes_get_armExecuteNever(vm_attributes_t vm_attributes)
{
	uint64_t ret;
	ret = (vm_attributes.words[0] & 0x4ull) >> 2;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t vm_attributes_get_armPageCacheable(vm_attributes_t vm_attributes)
{
	uint64_t ret;
	ret = (vm_attributes.words[0] & 0x1ull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
struct asid_map {
	uint64_t words[1];
};
typedef struct asid_map asid_map_t;
enum asid_map_tag { asid_map_asid_map_none = 0, asid_map_asid_map_vspace = 1 };
typedef enum asid_map_tag asid_map_tag_t;
static inline uint64_t asid_map_get_type(asid_map_t asid_map)
{
	return (asid_map.words[0] >> 0) & 0x1ull;
}
static inline asid_map_t asid_map_asid_map_none_new(void)
{
	asid_map_t asid_map;
	/* fail if user has passed bits that we will override */
	asid_map.words[0] = 0 | ((uint64_t)asid_map_asid_map_none & 0x1ull) << 0;
	return asid_map;
}
static inline asid_map_t asid_map_asid_map_vspace_new(uint64_t vspace_root)
{
	asid_map_t asid_map;
	/* fail if user has passed bits that we will override */
	asid_map.words[0] = 0 | (vspace_root & 0xfffffffff000ull) >> 0 |
			    ((uint64_t)asid_map_asid_map_vspace & 0x1ull) << 0;
	return asid_map;
}
static inline uint64_t asid_map_asid_map_vspace_get_vspace_root(asid_map_t asid_map)
{
	uint64_t ret;
	ret = (asid_map.words[0] & 0xfffffffff000ull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
struct cap {
	uint64_t words[2];
};
typedef struct cap cap_t;
enum cap_tag {
	cap_null_cap = 0,
	cap_untyped_cap = 2,
	cap_endpoint_cap = 4,
	cap_notification_cap = 6,
	cap_reply_cap = 8,
	cap_cnode_cap = 10,
	cap_thread_cap = 12,
	cap_irq_control_cap = 14,
	cap_irq_handler_cap = 16,
	cap_zombie_cap = 18,
	cap_domain_cap = 20,
	cap_frame_cap = 1,
	cap_page_table_cap = 3,
	cap_page_directory_cap = 5,
	cap_page_upper_directory_cap = 7,
	cap_page_global_directory_cap = 9,
	cap_asid_control_cap = 11,
	cap_asid_pool_cap = 13
};
typedef enum cap_tag cap_tag_t;
static inline uint64_t cap_get_capType(cap_t cap)
{
	return (cap.words[0] >> 59) & 0x1full;
}
static inline int cap_capType_equals(cap_t cap, uint64_t cap_type_tag)
{
	return ((cap.words[0] >> 59) & 0x1full) == cap_type_tag;
}
static inline cap_t cap_null_cap_new(void)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_null_cap & 0x1full) << 59;
	cap.words[1] = 0;
	return cap;
}
static inline cap_t cap_untyped_cap_new(uint64_t capFreeIndex, uint64_t capIsDevice,
					uint64_t capBlockSize, uint64_t capPtr)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] =
		0 | ((uint64_t)cap_untyped_cap & 0x1full) << 59 | (capPtr & 0xffffffffffffull) >> 0;
	cap.words[1] = 0 | (capFreeIndex & 0xffffffffffffull) << 16 | (capIsDevice & 0x1ull) << 6 |
		       (capBlockSize & 0x3full) << 0;
	return cap;
}
static inline uint64_t cap_untyped_cap_get_capFreeIndex(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffffffffffff0000ull) >> 16;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_untyped_cap_set_capFreeIndex(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[1] &= ~0xffffffffffff0000ull;
	cap.words[1] |= (v64 << 16) & 0xffffffffffff0000ull;
	return cap;
}
static inline void cap_untyped_cap_ptr_set_capFreeIndex(cap_t *cap_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[1] &= ~0xffffffffffff0000ull;
	cap_ptr->words[1] |= (v64 << 16) & 0xffffffffffff0000ull;
}
static inline uint64_t cap_untyped_cap_get_capIsDevice(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0x40ull) >> 6;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t cap_untyped_cap_get_capBlockSize(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0x3full) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t cap_untyped_cap_get_capPtr(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0xffffffffffffull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline cap_t cap_endpoint_cap_new(uint64_t capEPBadge, uint64_t capCanGrantReply,
					 uint64_t capCanGrant, uint64_t capCanSend,
					 uint64_t capCanReceive, uint64_t capEPPtr)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | (capCanGrantReply & 0x1ull) << 58 | (capCanGrant & 0x1ull) << 57 |
		       (capCanSend & 0x1ull) << 55 | (capCanReceive & 0x1ull) << 56 |
		       (capEPPtr & 0xffffffffffffull) >> 0 |
		       ((uint64_t)cap_endpoint_cap & 0x1full) << 59;
	cap.words[1] = 0 | capEPBadge << 0;
	return cap;
}
static inline uint64_t cap_endpoint_cap_get_capEPBadge(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_endpoint_cap_set_capEPBadge(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[1] &= ~0xffffffffffffffffull;
	cap.words[1] |= (v64 << 0) & 0xffffffffffffffffull;
	return cap;
}
static inline uint64_t cap_endpoint_cap_get_capCanGrantReply(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x400000000000000ull) >> 58;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_endpoint_cap_set_capCanGrantReply(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[0] &= ~0x400000000000000ull;
	cap.words[0] |= (v64 << 58) & 0x400000000000000ull;
	return cap;
}
static inline uint64_t cap_endpoint_cap_get_capCanGrant(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x200000000000000ull) >> 57;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_endpoint_cap_set_capCanGrant(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[0] &= ~0x200000000000000ull;
	cap.words[0] |= (v64 << 57) & 0x200000000000000ull;
	return cap;
}
static inline uint64_t cap_endpoint_cap_get_capCanReceive(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x100000000000000ull) >> 56;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_endpoint_cap_set_capCanReceive(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[0] &= ~0x100000000000000ull;
	cap.words[0] |= (v64 << 56) & 0x100000000000000ull;
	return cap;
}
static inline uint64_t cap_endpoint_cap_get_capCanSend(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x80000000000000ull) >> 55;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_endpoint_cap_set_capCanSend(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[0] &= ~0x80000000000000ull;
	cap.words[0] |= (v64 << 55) & 0x80000000000000ull;
	return cap;
}
static inline uint64_t cap_endpoint_cap_get_capEPPtr(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0xffffffffffffull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline cap_t cap_notification_cap_new(uint64_t capNtfnBadge, uint64_t capNtfnCanReceive,
					     uint64_t capNtfnCanSend, uint64_t capNtfnPtr)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_notification_cap & 0x1full) << 59 |
		       (capNtfnCanReceive & 0x1ull) << 58 | (capNtfnCanSend & 0x1ull) << 57 |
		       (capNtfnPtr & 0xffffffffffffull) >> 0;
	cap.words[1] = 0 | capNtfnBadge << 0;
	return cap;
}
static inline uint64_t cap_notification_cap_get_capNtfnBadge(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_notification_cap_set_capNtfnBadge(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[1] &= ~0xffffffffffffffffull;
	cap.words[1] |= (v64 << 0) & 0xffffffffffffffffull;
	return cap;
}
static inline uint64_t cap_notification_cap_get_capNtfnCanReceive(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x400000000000000ull) >> 58;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_notification_cap_set_capNtfnCanReceive(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[0] &= ~0x400000000000000ull;
	cap.words[0] |= (v64 << 58) & 0x400000000000000ull;
	return cap;
}
static inline uint64_t cap_notification_cap_get_capNtfnCanSend(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x200000000000000ull) >> 57;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_notification_cap_set_capNtfnCanSend(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[0] &= ~0x200000000000000ull;
	cap.words[0] |= (v64 << 57) & 0x200000000000000ull;
	return cap;
}
static inline uint64_t cap_notification_cap_get_capNtfnPtr(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0xffffffffffffull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline cap_t cap_reply_cap_new(uint64_t capReplyCanGrant, uint64_t capReplyMaster,
				      uint64_t capTCBPtr)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | (capReplyCanGrant & 0x1ull) << 1 | (capReplyMaster & 0x1ull) << 0 |
		       ((uint64_t)cap_reply_cap & 0x1full) << 59;
	cap.words[1] = 0 | capTCBPtr << 0;
	return cap;
}
static inline uint64_t cap_reply_cap_get_capTCBPtr(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t cap_reply_cap_get_capReplyCanGrant(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x2ull) >> 1;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_reply_cap_set_capReplyCanGrant(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[0] &= ~0x2ull;
	cap.words[0] |= (v64 << 1) & 0x2ull;
	return cap;
}
static inline uint64_t cap_reply_cap_get_capReplyMaster(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x1ull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_cnode_cap_new(uint64_t capCNodeRadix, uint64_t capCNodeGuardSize,
				      uint64_t capCNodeGuard, uint64_t capCNodePtr)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | (capCNodeRadix & 0x3full) << 47 | (capCNodeGuardSize & 0x3full) << 53 |
		       (capCNodePtr & 0xfffffffffffeull) >> 1 |
		       ((uint64_t)cap_cnode_cap & 0x1full) << 59;
	cap.words[1] = 0 | capCNodeGuard << 0;
	return cap;
}
static inline uint64_t cap_cnode_cap_get_capCNodeGuard(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_cnode_cap_set_capCNodeGuard(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[1] &= ~0xffffffffffffffffull;
	cap.words[1] |= (v64 << 0) & 0xffffffffffffffffull;
	return cap;
}
static inline uint64_t cap_cnode_cap_get_capCNodeGuardSize(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x7e0000000000000ull) >> 53;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_cnode_cap_set_capCNodeGuardSize(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[0] &= ~0x7e0000000000000ull;
	cap.words[0] |= (v64 << 53) & 0x7e0000000000000ull;
	return cap;
}
static inline uint64_t cap_cnode_cap_get_capCNodeRadix(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x1f800000000000ull) >> 47;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t cap_cnode_cap_get_capCNodePtr(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x7fffffffffffull) << 1;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline cap_t cap_thread_cap_new(uint64_t capTCBPtr)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_thread_cap & 0x1full) << 59 |
		       (capTCBPtr & 0xffffffffffffull) >> 0;
	cap.words[1] = 0;
	return cap;
}
static inline uint64_t cap_thread_cap_get_capTCBPtr(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0xffffffffffffull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline cap_t cap_irq_control_cap_new(void)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_irq_control_cap & 0x1full) << 59;
	cap.words[1] = 0;
	return cap;
}
static inline cap_t cap_irq_handler_cap_new(uint64_t capIRQ)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_irq_handler_cap & 0x1full) << 59;
	cap.words[1] = 0 | (capIRQ & 0xfffull) << 0;
	return cap;
}
static inline uint64_t cap_irq_handler_cap_get_capIRQ(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xfffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_zombie_cap_new(uint64_t capZombieID, uint64_t capZombieType)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] =
		0 | ((uint64_t)cap_zombie_cap & 0x1full) << 59 | (capZombieType & 0x7full) << 0;
	cap.words[1] = 0 | capZombieID << 0;
	return cap;
}
static inline uint64_t cap_zombie_cap_get_capZombieID(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_zombie_cap_set_capZombieID(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[1] &= ~0xffffffffffffffffull;
	cap.words[1] |= (v64 << 0) & 0xffffffffffffffffull;
	return cap;
}
static inline uint64_t cap_zombie_cap_get_capZombieType(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x7full) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_domain_cap_new(void)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_domain_cap & 0x1full) << 59;
	cap.words[1] = 0;
	return cap;
}
static inline cap_t cap_frame_cap_new(uint64_t capFMappedASID, uint64_t capFBasePtr,
				      uint64_t capFSize, uint64_t capFMappedAddress,
				      uint64_t capFVMRights, uint64_t capFIsDevice)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_frame_cap & 0x1full) << 59 | (capFSize & 0x3ull) << 57 |
		       (capFMappedAddress & 0xffffffffffffull) << 9 | (capFVMRights & 0x3ull) << 7 |
		       (capFIsDevice & 0x1ull) << 6;
	cap.words[1] =
		0 | (capFMappedASID & 0xffffull) << 48 | (capFBasePtr & 0xffffffffffffull) >> 0;
	return cap;
}
static inline uint64_t cap_frame_cap_get_capFMappedASID(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffff000000000000ull) >> 48;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_frame_cap_set_capFMappedASID(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[1] &= ~0xffff000000000000ull;
	cap.words[1] |= (v64 << 48) & 0xffff000000000000ull;
	return cap;
}
static inline uint64_t cap_frame_cap_ptr_get_capFMappedASID(cap_t *cap_ptr)
{
	uint64_t ret;
	ret = (cap_ptr->words[1] & 0xffff000000000000ull) >> 48;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void cap_frame_cap_ptr_set_capFMappedASID(cap_t *cap_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[1] &= ~0xffff000000000000ull;
	cap_ptr->words[1] |= (v64 << 48) & 0xffff000000000000ull;
}
static inline uint64_t cap_frame_cap_get_capFBasePtr(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffffffffffffull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline uint64_t cap_frame_cap_get_capFSize(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x600000000000000ull) >> 57;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t cap_frame_cap_get_capFMappedAddress(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x1fffffffffffe00ull) >> 9;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline cap_t cap_frame_cap_set_capFMappedAddress(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[0] &= ~0x1fffffffffffe00ull;
	cap.words[0] |= (v64 << 9) & 0x1fffffffffffe00ull;
	return cap;
}
static inline void cap_frame_cap_ptr_set_capFMappedAddress(cap_t *cap_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[0] &= ~0x1fffffffffffe00ull;
	cap_ptr->words[0] |= (v64 << 9) & 0x1fffffffffffe00ull;
}
static inline uint64_t cap_frame_cap_get_capFVMRights(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x180ull) >> 7;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_frame_cap_set_capFVMRights(cap_t cap, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap.words[0] &= ~0x180ull;
	cap.words[0] |= (v64 << 7) & 0x180ull;
	return cap;
}
static inline uint64_t cap_frame_cap_get_capFIsDevice(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x40ull) >> 6;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline cap_t cap_page_table_cap_new(uint64_t capPTMappedASID, uint64_t capPTBasePtr,
					   uint64_t capPTIsMapped, uint64_t capPTMappedAddress)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_page_table_cap & 0x1full) << 59 |
		       (capPTIsMapped & 0x1ull) << 48 |
		       (capPTMappedAddress & 0xfffffff00000ull) >> 0;
	cap.words[1] =
		0 | (capPTMappedASID & 0xffffull) << 48 | (capPTBasePtr & 0xffffffffffffull) >> 0;
	return cap;
}
static inline uint64_t cap_page_table_cap_get_capPTMappedASID(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffff000000000000ull) >> 48;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void cap_page_table_cap_ptr_set_capPTMappedASID(cap_t *cap_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[1] &= ~0xffff000000000000ull;
	cap_ptr->words[1] |= (v64 << 48) & 0xffff000000000000ull;
}
static inline uint64_t cap_page_table_cap_get_capPTBasePtr(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffffffffffffull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline uint64_t cap_page_table_cap_get_capPTIsMapped(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x1000000000000ull) >> 48;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void cap_page_table_cap_ptr_set_capPTIsMapped(cap_t *cap_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[0] &= ~0x1000000000000ull;
	cap_ptr->words[0] |= (v64 << 48) & 0x1000000000000ull;
}
static inline uint64_t cap_page_table_cap_get_capPTMappedAddress(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0xfffffff00000ull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline void cap_page_table_cap_ptr_set_capPTMappedAddress(cap_t *cap_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[0] &= ~0xfffffff00000ull;
	cap_ptr->words[0] |= (v64 >> 0) & 0xfffffff00000ull;
}
static inline cap_t cap_page_directory_cap_new(uint64_t capPDMappedASID, uint64_t capPDBasePtr,
					       uint64_t capPDIsMapped, uint64_t capPDMappedAddress)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_page_directory_cap & 0x1full) << 59 |
		       (capPDIsMapped & 0x1ull) << 48 |
		       (capPDMappedAddress & 0xffffe0000000ull) >> 0;
	cap.words[1] =
		0 | (capPDMappedASID & 0xffffull) << 48 | (capPDBasePtr & 0xffffffffffffull) >> 0;
	return cap;
}
static inline uint64_t cap_page_directory_cap_get_capPDMappedASID(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffff000000000000ull) >> 48;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void cap_page_directory_cap_ptr_set_capPDMappedASID(cap_t *cap_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[1] &= ~0xffff000000000000ull;
	cap_ptr->words[1] |= (v64 << 48) & 0xffff000000000000ull;
}
static inline uint64_t cap_page_directory_cap_get_capPDBasePtr(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffffffffffffull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline uint64_t cap_page_directory_cap_get_capPDIsMapped(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x1000000000000ull) >> 48;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void cap_page_directory_cap_ptr_set_capPDIsMapped(cap_t *cap_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[0] &= ~0x1000000000000ull;
	cap_ptr->words[0] |= (v64 << 48) & 0x1000000000000ull;
}
static inline uint64_t cap_page_directory_cap_get_capPDMappedAddress(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0xffffe0000000ull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline void cap_page_directory_cap_ptr_set_capPDMappedAddress(cap_t *cap_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[0] &= ~0xffffe0000000ull;
	cap_ptr->words[0] |= (v64 >> 0) & 0xffffe0000000ull;
}
static inline cap_t cap_page_upper_directory_cap_new(uint64_t capPUDMappedASID,
						     uint64_t capPUDBasePtr,
						     uint64_t capPUDIsMapped,
						     uint64_t capPUDMappedAddress)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_page_upper_directory_cap & 0x1full) << 59 |
		       (capPUDIsMapped & 0x1ull) << 58 |
		       (capPUDMappedAddress & 0xffc000000000ull) << 10;
	cap.words[1] =
		0 | (capPUDMappedASID & 0xffffull) << 48 | (capPUDBasePtr & 0xffffffffffffull) >> 0;
	return cap;
}
static inline uint64_t cap_page_upper_directory_cap_get_capPUDMappedASID(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffff000000000000ull) >> 48;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void cap_page_upper_directory_cap_ptr_set_capPUDMappedASID(cap_t *cap_ptr,
									 uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[1] &= ~0xffff000000000000ull;
	cap_ptr->words[1] |= (v64 << 48) & 0xffff000000000000ull;
}
static inline uint64_t cap_page_upper_directory_cap_get_capPUDBasePtr(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffffffffffffull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline uint64_t cap_page_upper_directory_cap_get_capPUDIsMapped(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x400000000000000ull) >> 58;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void cap_page_upper_directory_cap_ptr_set_capPUDIsMapped(cap_t *cap_ptr, uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[0] &= ~0x400000000000000ull;
	cap_ptr->words[0] |= (v64 << 58) & 0x400000000000000ull;
}
static inline uint64_t cap_page_upper_directory_cap_get_capPUDMappedAddress(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x3ff000000000000ull) >> 10;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline void cap_page_upper_directory_cap_ptr_set_capPUDMappedAddress(cap_t *cap_ptr,
									    uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[0] &= ~0x3ff000000000000ull;
	cap_ptr->words[0] |= (v64 << 10) & 0x3ff000000000000ull;
}
static inline cap_t cap_page_global_directory_cap_new(uint64_t capPGDMappedASID,
						      uint64_t capPGDBasePtr,
						      uint64_t capPGDIsMapped)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_page_global_directory_cap & 0x1full) << 59 |
		       (capPGDIsMapped & 0x1ull) << 58;
	cap.words[1] =
		0 | (capPGDMappedASID & 0xffffull) << 48 | (capPGDBasePtr & 0xffffffffffffull) >> 0;
	return cap;
}
static inline uint64_t cap_page_global_directory_cap_get_capPGDMappedASID(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffff000000000000ull) >> 48;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void cap_page_global_directory_cap_ptr_set_capPGDMappedASID(cap_t *cap_ptr,
									  uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[1] &= ~0xffff000000000000ull;
	cap_ptr->words[1] |= (v64 << 48) & 0xffff000000000000ull;
}
static inline uint64_t cap_page_global_directory_cap_get_capPGDBasePtr(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[1] & 0xffffffffffffull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
static inline uint64_t cap_page_global_directory_cap_get_capPGDIsMapped(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x400000000000000ull) >> 58;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline void cap_page_global_directory_cap_ptr_set_capPGDIsMapped(cap_t *cap_ptr,
									uint64_t v64)
{
	/* fail if user has passed bits that we will override */
	cap_ptr->words[0] &= ~0x400000000000000ull;
	cap_ptr->words[0] |= (v64 << 58) & 0x400000000000000ull;
}
static inline cap_t cap_asid_control_cap_new(void)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_asid_control_cap & 0x1full) << 59;
	cap.words[1] = 0;
	return cap;
}
static inline cap_t cap_asid_pool_cap_new(uint64_t capASIDBase, uint64_t capASIDPool)
{
	cap_t cap;
	/* fail if user has passed bits that we will override */
	cap.words[0] = 0 | ((uint64_t)cap_asid_pool_cap & 0x1full) << 59 |
		       (capASIDBase & 0xffffull) << 43 | (capASIDPool & 0xfffffffff800ull) >> 11;
	cap.words[1] = 0;
	return cap;
}
static inline uint64_t cap_asid_pool_cap_get_capASIDBase(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x7fff80000000000ull) >> 43;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t cap_asid_pool_cap_get_capASIDPool(cap_t cap)
{
	uint64_t ret;
	ret = (cap.words[0] & 0x1fffffffffull) << 11;
	/* Possibly sign extend */
	if (__builtin_expect(!!(1 && (ret & (1ull << (47)))), 1)) {
		ret |= 0xffff000000000000;
	}
	return ret;
}
struct lookup_fault {
	uint64_t words[2];
};
typedef struct lookup_fault lookup_fault_t;
enum lookup_fault_tag {
	lookup_fault_invalid_root = 0,
	lookup_fault_missing_capability = 1,
	lookup_fault_depth_mismatch = 2,
	lookup_fault_guard_mismatch = 3
};
typedef enum lookup_fault_tag lookup_fault_tag_t;
static inline uint64_t lookup_fault_get_lufType(lookup_fault_t lookup_fault)
{
	return (lookup_fault.words[0] >> 0) & 0x3ull;
}
static inline lookup_fault_t lookup_fault_invalid_root_new(void)
{
	lookup_fault_t lookup_fault;
	/* fail if user has passed bits that we will override */
	lookup_fault.words[0] = 0 | ((uint64_t)lookup_fault_invalid_root & 0x3ull) << 0;
	lookup_fault.words[1] = 0;
	return lookup_fault;
}
static inline lookup_fault_t lookup_fault_missing_capability_new(uint64_t bitsLeft)
{
	lookup_fault_t lookup_fault;
	/* fail if user has passed bits that we will override */
	lookup_fault.words[0] = 0 | (bitsLeft & 0x7full) << 2 |
				((uint64_t)lookup_fault_missing_capability & 0x3ull) << 0;
	lookup_fault.words[1] = 0;
	return lookup_fault;
}
static inline uint64_t lookup_fault_missing_capability_get_bitsLeft(lookup_fault_t lookup_fault)
{
	uint64_t ret;
	ret = (lookup_fault.words[0] & 0x1fcull) >> 2;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline lookup_fault_t lookup_fault_depth_mismatch_new(uint64_t bitsFound, uint64_t bitsLeft)
{
	lookup_fault_t lookup_fault;
	/* fail if user has passed bits that we will override */
	lookup_fault.words[0] = 0 | (bitsFound & 0x7full) << 9 | (bitsLeft & 0x7full) << 2 |
				((uint64_t)lookup_fault_depth_mismatch & 0x3ull) << 0;
	lookup_fault.words[1] = 0;
	return lookup_fault;
}
static inline uint64_t lookup_fault_depth_mismatch_get_bitsFound(lookup_fault_t lookup_fault)
{
	uint64_t ret;
	ret = (lookup_fault.words[0] & 0xfe00ull) >> 9;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t lookup_fault_depth_mismatch_get_bitsLeft(lookup_fault_t lookup_fault)
{
	uint64_t ret;
	ret = (lookup_fault.words[0] & 0x1fcull) >> 2;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline lookup_fault_t lookup_fault_guard_mismatch_new(uint64_t guardFound, uint64_t bitsLeft,
							     uint64_t bitsFound)
{
	lookup_fault_t lookup_fault;
	/* fail if user has passed bits that we will override */
	lookup_fault.words[0] = 0 | (bitsLeft & 0x7full) << 9 | (bitsFound & 0x7full) << 2 |
				((uint64_t)lookup_fault_guard_mismatch & 0x3ull) << 0;
	lookup_fault.words[1] = 0 | guardFound << 0;
	return lookup_fault;
}
static inline uint64_t lookup_fault_guard_mismatch_get_guardFound(lookup_fault_t lookup_fault)
{
	uint64_t ret;
	ret = (lookup_fault.words[1] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t lookup_fault_guard_mismatch_get_bitsLeft(lookup_fault_t lookup_fault)
{
	uint64_t ret;
	ret = (lookup_fault.words[0] & 0xfe00ull) >> 9;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t lookup_fault_guard_mismatch_get_bitsFound(lookup_fault_t lookup_fault)
{
	uint64_t ret;
	ret = (lookup_fault.words[0] & 0x1fcull) >> 2;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
struct pde {
	uint64_t words[1];
};
typedef struct pde pde_t;
enum pde_tag { pde_pde_large = 1, pde_pde_small = 3 };
typedef enum pde_tag pde_tag_t;
static inline uint64_t pde_ptr_get_pde_type(pde_t *pde_ptr)
{
	return (pde_ptr->words[0] >> 0) & 0x3ull;
}
static inline pde_t pde_pde_large_new(uint64_t UXN, uint64_t page_base_address, uint64_t nG,
				      uint64_t AF, uint64_t SH, uint64_t AP, uint64_t AttrIndx)
{
	pde_t pde;
	/* fail if user has passed bits that we will override */
	pde.words[0] = 0 | (UXN & 0x1ull) << 54 | (page_base_address & 0xffffffe00000ull) >> 0 |
		       (nG & 0x1ull) << 11 | (AF & 0x1ull) << 10 | (SH & 0x3ull) << 8 |
		       (AP & 0x3ull) << 6 | (AttrIndx & 0x7ull) << 2 |
		       ((uint64_t)pde_pde_large & 0x3ull) << 0;
	return pde;
}
static inline uint64_t pde_pde_large_ptr_get_UXN(pde_t *pde_ptr)
{
	uint64_t ret;
	ret = (pde_ptr->words[0] & 0x40000000000000ull) >> 54;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t pde_pde_large_ptr_get_page_base_address(pde_t *pde_ptr)
{
	uint64_t ret;
	ret = (pde_ptr->words[0] & 0xffffffe00000ull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t pde_pde_large_ptr_get_SH(pde_t *pde_ptr)
{
	uint64_t ret;
	ret = (pde_ptr->words[0] & 0x300ull) >> 8;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t pde_pde_large_ptr_get_AP(pde_t *pde_ptr)
{
	uint64_t ret;
	ret = (pde_ptr->words[0] & 0xc0ull) >> 6;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline pde_t pde_pde_small_new(uint64_t pt_base_address)
{
	pde_t pde;
	/* fail if user has passed bits that we will override */
	pde.words[0] = 0 | (pt_base_address & 0xfffffffff000ull) >> 0 |
		       ((uint64_t)pde_pde_small & 0x3ull) << 0;
	return pde;
}
static inline uint64_t pde_pde_small_ptr_get_pt_base_address(pde_t *pde_ptr)
{
	uint64_t ret;
	ret = (pde_ptr->words[0] & 0xfffffffff000ull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
struct pgde {
	uint64_t words[1];
};
typedef struct pgde pgde_t;
enum pgde_tag { pgde_pgde_invalid = 0, pgde_pgde_pud = 3 };
typedef enum pgde_tag pgde_tag_t;
static inline uint64_t pgde_ptr_get_pgde_type(pgde_t *pgde_ptr)
{
	return (pgde_ptr->words[0] >> 0) & 0x3ull;
}
static inline pgde_t pgde_pgde_invalid_new(void)
{
	pgde_t pgde;
	/* fail if user has passed bits that we will override */
	pgde.words[0] = 0 | ((uint64_t)pgde_pgde_invalid & 0x3ull) << 0;
	return pgde;
}
static inline pgde_t pgde_pgde_pud_new(uint64_t pud_base_address)
{
	pgde_t pgde;
	/* fail if user has passed bits that we will override */
	pgde.words[0] = 0 | (pud_base_address & 0xfffffffff000ull) >> 0 |
			((uint64_t)pgde_pgde_pud & 0x3ull) << 0;
	return pgde;
}
static inline uint64_t pgde_pgde_pud_ptr_get_pud_base_address(pgde_t *pgde_ptr)
{
	uint64_t ret;
	ret = (pgde_ptr->words[0] & 0xfffffffff000ull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
struct pude {
	uint64_t words[1];
};
typedef struct pude pude_t;
enum pude_tag { pude_pude_invalid = 0, pude_pude_1g = 1, pude_pude_pd = 3 };
typedef enum pude_tag pude_tag_t;
static inline uint64_t pude_ptr_get_pude_type(pude_t *pude_ptr)
{
	return (pude_ptr->words[0] >> 0) & 0x3ull;
}
static inline pude_t pude_pude_1g_new(uint64_t UXN, uint64_t page_base_address, uint64_t nG,
				      uint64_t AF, uint64_t SH, uint64_t AP, uint64_t AttrIndx)
{
	pude_t pude;
	/* fail if user has passed bits that we will override */
	pude.words[0] = 0 | (UXN & 0x1ull) << 54 | (page_base_address & 0xffffc0000000ull) >> 0 |
			(nG & 0x1ull) << 11 | (AF & 0x1ull) << 10 | (SH & 0x3ull) << 8 |
			(AP & 0x3ull) << 6 | (AttrIndx & 0x7ull) << 2 |
			((uint64_t)pude_pude_1g & 0x3ull) << 0;
	return pude;
}
static inline uint64_t pude_pude_1g_ptr_get_UXN(pude_t *pude_ptr)
{
	uint64_t ret;
	ret = (pude_ptr->words[0] & 0x40000000000000ull) >> 54;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t pude_pude_1g_ptr_get_page_base_address(pude_t *pude_ptr)
{
	uint64_t ret;
	ret = (pude_ptr->words[0] & 0xffffc0000000ull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t pude_pude_1g_ptr_get_SH(pude_t *pude_ptr)
{
	uint64_t ret;
	ret = (pude_ptr->words[0] & 0x300ull) >> 8;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t pude_pude_1g_ptr_get_AP(pude_t *pude_ptr)
{
	uint64_t ret;
	ret = (pude_ptr->words[0] & 0xc0ull) >> 6;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline pude_t pude_pude_pd_new(uint64_t pd_base_address)
{
	pude_t pude;
	/* fail if user has passed bits that we will override */
	pude.words[0] = 0 | (pd_base_address & 0xfffffffff000ull) >> 0 |
			((uint64_t)pude_pude_pd & 0x3ull) << 0;
	return pude;
}
static inline uint64_t pude_pude_pd_ptr_get_pd_base_address(pude_t *pude_ptr)
{
	uint64_t ret;
	ret = (pude_ptr->words[0] & 0xfffffffff000ull) << 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
struct seL4_Fault {
	uint64_t words[2];
};
typedef struct seL4_Fault seL4_Fault_t;
enum seL4_Fault_tag {
	seL4_Fault_NullFault = 0,
	seL4_Fault_CapFault = 1,
	seL4_Fault_UnknownSyscall = 2,
	seL4_Fault_UserException = 3,
	seL4_Fault_VMFault = 5
};
typedef enum seL4_Fault_tag seL4_Fault_tag_t;
static inline uint64_t seL4_Fault_get_seL4_FaultType(seL4_Fault_t seL4_Fault)
{
	return (seL4_Fault.words[0] >> 0) & 0xfull;
}
static inline seL4_Fault_t seL4_Fault_NullFault_new(void)
{
	seL4_Fault_t seL4_Fault;
	/* fail if user has passed bits that we will override */
	seL4_Fault.words[0] = 0 | ((uint64_t)seL4_Fault_NullFault & 0xfull) << 0;
	seL4_Fault.words[1] = 0;
	return seL4_Fault;
}
static inline seL4_Fault_t seL4_Fault_CapFault_new(uint64_t address, uint64_t inReceivePhase)
{
	seL4_Fault_t seL4_Fault;
	/* fail if user has passed bits that we will override */
	seL4_Fault.words[0] =
		0 | (inReceivePhase & 0x1ull) << 63 | ((uint64_t)seL4_Fault_CapFault & 0xfull) << 0;
	seL4_Fault.words[1] = 0 | address << 0;
	return seL4_Fault;
}
static inline uint64_t seL4_Fault_CapFault_get_address(seL4_Fault_t seL4_Fault)
{
	uint64_t ret;
	ret = (seL4_Fault.words[1] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t seL4_Fault_CapFault_get_inReceivePhase(seL4_Fault_t seL4_Fault)
{
	uint64_t ret;
	ret = (seL4_Fault.words[0] & 0x8000000000000000ull) >> 63;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline seL4_Fault_t seL4_Fault_UnknownSyscall_new(uint64_t syscallNumber)
{
	seL4_Fault_t seL4_Fault;
	/* fail if user has passed bits that we will override */
	seL4_Fault.words[0] = 0 | ((uint64_t)seL4_Fault_UnknownSyscall & 0xfull) << 0;
	seL4_Fault.words[1] = 0 | syscallNumber << 0;
	return seL4_Fault;
}
static inline uint64_t seL4_Fault_UnknownSyscall_get_syscallNumber(seL4_Fault_t seL4_Fault)
{
	uint64_t ret;
	ret = (seL4_Fault.words[1] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline seL4_Fault_t seL4_Fault_UserException_new(uint64_t number, uint64_t code)
{
	seL4_Fault_t seL4_Fault;
	/* fail if user has passed bits that we will override */
	seL4_Fault.words[0] = 0 | (number & 0xffffffffull) << 32 | (code & 0xfffffffull) << 4 |
			      ((uint64_t)seL4_Fault_UserException & 0xfull) << 0;
	seL4_Fault.words[1] = 0;
	return seL4_Fault;
}
static inline uint64_t seL4_Fault_UserException_get_number(seL4_Fault_t seL4_Fault)
{
	uint64_t ret;
	ret = (seL4_Fault.words[0] & 0xffffffff00000000ull) >> 32;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t seL4_Fault_UserException_get_code(seL4_Fault_t seL4_Fault)
{
	uint64_t ret;
	ret = (seL4_Fault.words[0] & 0xfffffff0ull) >> 4;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline seL4_Fault_t seL4_Fault_VMFault_new(uint64_t address, uint64_t FSR,
						  uint64_t instructionFault)
{
	seL4_Fault_t seL4_Fault;
	/* fail if user has passed bits that we will override */
	seL4_Fault.words[0] = 0 | (FSR & 0xffffffffull) << 32 | (instructionFault & 0x1ull) << 31 |
			      ((uint64_t)seL4_Fault_VMFault & 0xfull) << 0;
	seL4_Fault.words[1] = 0 | address << 0;
	return seL4_Fault;
}
static inline uint64_t seL4_Fault_VMFault_get_address(seL4_Fault_t seL4_Fault)
{
	uint64_t ret;
	ret = (seL4_Fault.words[1] & 0xffffffffffffffffull) >> 0;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t seL4_Fault_VMFault_get_FSR(seL4_Fault_t seL4_Fault)
{
	uint64_t ret;
	ret = (seL4_Fault.words[0] & 0xffffffff00000000ull) >> 32;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
static inline uint64_t seL4_Fault_VMFault_get_instructionFault(seL4_Fault_t seL4_Fault)
{
	uint64_t ret;
	ret = (seL4_Fault.words[0] & 0x80000000ull) >> 31;
	/* Possibly sign extend */
	if (__builtin_expect(!!(0 && (ret & (1ull << (47)))), 0)) {
		ret |= 0x0;
	}
	return ret;
}
/* format of an unknown syscall message */
typedef enum {
	seL4_UnknownSyscall_X0,
	seL4_UnknownSyscall_X1,
	seL4_UnknownSyscall_X2,
	seL4_UnknownSyscall_X3,
	seL4_UnknownSyscall_X4,
	seL4_UnknownSyscall_X5,
	seL4_UnknownSyscall_X6,
	seL4_UnknownSyscall_X7,
	seL4_UnknownSyscall_FaultIP,
	seL4_UnknownSyscall_SP,
	seL4_UnknownSyscall_LR,
	seL4_UnknownSyscall_SPSR,
	seL4_UnknownSyscall_Syscall,
	/* length of an unknown syscall message */
	seL4_UnknownSyscall_Length,
	_enum_pad_seL4_UnknownSyscall_Msg = ((1ULL << ((sizeof(long) * 8) - 1)) - 1),
} seL4_UnknownSyscall_Msg;
/* format of a user exception message */
typedef enum {
	seL4_UserException_FaultIP,
	seL4_UserException_SP,
	seL4_UserException_SPSR,
	seL4_UserException_Number,
	seL4_UserException_Code,
	/* length of a user exception */
	seL4_UserException_Length,
	_enum_pad_seL4_UserException_Msg = ((1ULL << ((sizeof(long) * 8) - 1)) - 1),
} seL4_UserException_Msg;
/* format of a vm fault message */
typedef enum {
	seL4_VMFault_IP,
	seL4_VMFault_Addr,
	seL4_VMFault_PrefetchFault,
	seL4_VMFault_FSR,
	seL4_VMFault_Length,
	_enum_pad_seL4_VMFault_Msg = ((1ULL << ((sizeof(long) * 8) - 1)) - 1),
} seL4_VMFault_Msg;
/* object sizes - 2^n */
/* word size */
/* Untyped size limits */
typedef int __assert_failed_seL4_PageTableEntryBits_seL4_PageTableIndexBits_seL4_PageTableBits
	[((3) + (9) == 12) ? 1 : -1];
;
typedef int __assert_failed_seL4_PageDirEntryBits_seL4_PageDirIndexBits_seL4_PageDirBits
	[((3) + (9) == 12) ? 1 : -1];
;
typedef int __assert_failed_seL4_WordSizeBits_seL4_ASIDPoolIndexBits_seL4_ASIDPoolBits
	[((3) + (9) == 12) ? 1 : -1];
;
typedef int __assert_failed_seL4_PGDEntryBits_seL4_PGDIndexBits_seL4_PGDBits[((3) + (9) == 12)
										     ? 1
										     : -1];
;
typedef int __assert_failed_seL4_PUDEntryBits_seL4_PUDIndexBits_seL4_PUDBits[((3) + (9) == 12)
										     ? 1
										     : -1];
;
/* IPC buffer is 1024 bytes, giving size bits of 10 */
/* First address in the virtual address space that is not accessible to user level */
enum irq_state { IRQInactive = 0, IRQSignal = 1, IRQTimer = 2, IRQReserved };
typedef word_t irq_state_t;
typedef struct dschedule {
	dom_t domain;
	word_t length;
} dschedule_t;
enum asidSizeConstants { asidHighBits = 7, asidLowBits = 9 };
/* Arch-independent object types */
enum endpoint_state { EPState_Idle = 0, EPState_Send = 1, EPState_Recv = 2 };
typedef word_t endpoint_state_t;
enum notification_state { NtfnState_Idle = 0, NtfnState_Waiting = 1, NtfnState_Active = 2 };
typedef word_t notification_state_t;
// We would like the actual 'tcb' region (the portion that contains the tcb_t) of the tcb
// to be as large as possible, but it still needs to be aligned. As the TCB object contains
// two sub objects the largest we can make either sub object whilst preserving size alignment
// is half the total size. To halve an object size defined in bits we just subtract 1
//
// A diagram of a TCB kernel object that is created from untyped:
//  _______________________________________
// |     |             |                   |
// |     |             |                   |
// |cte_t|   unused    |       tcb_t       |
// |     |(debug_tcb_t)|                   |
// |_____|_____________|___________________|
// 0     a             b                   c
// a = tcbCNodeEntries * sizeof(cte_t)
// b = BIT(TCB_SIZE_BITS)
// c = BIT(seL4_TCBBits)
//
/* Generate a tcb_t or cte_t pointer from a tcb block reference */
/* Generate a cte_t pointer from a tcb_t pointer */
static inline cap_t Zombie_new(word_t number, word_t type, word_t ptr)
{
	word_t mask;
	if (type == (1ul << (6))) {
		mask = ((1ul << (4 + 1)) - 1ul);
	} else {
		mask = ((1ul << (type + 1)) - 1ul);
	}
	return cap_zombie_cap_new((ptr & ~mask) | (number & mask), type);
}
static inline word_t cap_zombie_cap_get_capZombieBits(cap_t cap)
{
	word_t type = cap_zombie_cap_get_capZombieType(cap);
	if (type == (1ul << (6))) {
		return 4;
	}
	return ((type) & ((1ul << (6)) - 1ul)); /* cnode radix */
}
static inline word_t cap_zombie_cap_get_capZombieNumber(cap_t cap)
{
	word_t radix = cap_zombie_cap_get_capZombieBits(cap);
	return cap_zombie_cap_get_capZombieID(cap) & ((1ul << (radix + 1)) - 1ul);
}
static inline word_t cap_zombie_cap_get_capZombiePtr(cap_t cap)
{
	word_t radix = cap_zombie_cap_get_capZombieBits(cap);
	return cap_zombie_cap_get_capZombieID(cap) & ~((1ul << (radix + 1)) - 1ul);
}
static inline cap_t cap_zombie_cap_set_capZombieNumber(cap_t cap, word_t n)
{
	word_t radix = cap_zombie_cap_get_capZombieBits(cap);
	word_t ptr = cap_zombie_cap_get_capZombieID(cap) & ~((1ul << (radix + 1)) - 1ul);
	return cap_zombie_cap_set_capZombieID(cap, ptr | (n & ((1ul << (radix + 1)) - 1ul)));
}
/* Capability table entry (CTE) */
struct cte {
	cap_t cap;
	mdb_node_t cteMDBNode;
};
typedef struct cte cte_t;
/* Thread state */
enum _thread_state {
	ThreadState_Inactive = 0,
	ThreadState_Running,
	ThreadState_Restart,
	ThreadState_BlockedOnReceive,
	ThreadState_BlockedOnSend,
	ThreadState_BlockedOnReply,
	ThreadState_BlockedOnNotification,
	ThreadState_IdleThreadState
};
typedef word_t _thread_state_t;
/* A TCB CNode and a TCB are always allocated together, and adjacently.
 * The CNode comes first. */
enum tcb_cnode_index {
	/* CSpace root */
	tcbCTable = 0,
	/* VSpace root */
	tcbVTable = 1,
	/* Reply cap slot */
	tcbReply = 2,
	/* TCB of most recent IPC sender */
	tcbCaller = 3,
	/* IPC buffer cap slot */
	tcbBuffer = 4,
	tcbCNodeEntries
};
typedef word_t tcb_cnode_index_t;
/* Control register fields */
enum vm_page_size { ARMSmallPage, ARMLargePage, ARMHugePage };
typedef word_t vm_page_size_t;
enum frameSizeConstants { ARMSmallPageBits = 12, ARMLargePageBits = 21, ARMHugePageBits = 30 };
static inline word_t pageBitsForSize(vm_page_size_t pagesize)
{
	switch (pagesize) {
	case ARMSmallPage:
		return ARMSmallPageBits;
	case ARMLargePage:
		return ARMLargePageBits;
	case ARMHugePage:
		return ARMHugePageBits;
	default:
		_fail("Invalid page size",
		      "/home/lab/projects/seL4/seL4test/kernel/include/arch/arm/arch/64/mode/"
		      "machine/hardware.h",
		      54, __func__);
	}
}
enum vm_fault_type { ARMDataAbort = 0, ARMPrefetchAbort = 1 };
typedef word_t vm_fault_type_t;
/* CurrentEL register */
/* PSTATE register */
/* DAIF register */
/* ESR register */
/* ID_AA64PFR0_EL1 register */
/* CPACR_EL1 register */
/*
 * We cannot allow async aborts in the verified kernel, but they are useful
 * in identifying invalid memory access bugs so we enable them in debug mode.
 */
/* Offsets within the user context, these need to match the order in
 * register_t below */
/* The QEMU virt platform can emulate various cores */
/* Cortex-A53 Manual, Section 11.6.1 */
/* First address in the virtual address space that is not accessible to user level */
/* These are the indices of the registers in the saved thread context.
 * The values are determined by the order in which they're saved in the trap handler. */
enum _register {
	X0 = 0, /* 0x00 */
	capRegister = 0,
	badgeRegister = 0,
	X1 = 1, /* 0x08 */
	msgInfoRegister = 1,
	X2 = 2,	  /* 0x10 */
	X3 = 3,	  /* 0x18 */
	X4 = 4,	  /* 0x20 */
	X5 = 5,	  /* 0x28 */
	X6 = 6,	  /* 0x30 */
	X7 = 7,	  /* 0x38 */
	X8 = 8,	  /* 0x40 */
	X9 = 9,	  /* 0x48 */
	X10 = 10, /* 0x50 */
	X11 = 11, /* 0x58 */
	X12 = 12, /* 0x60 */
	X13 = 13, /* 0x68 */
	X14 = 14, /* 0x70 */
	X15 = 15, /* 0x78 */
	X16 = 16, /* 0x80 */
	X17 = 17, /* 0x88 */
	X18 = 18, /* 0x90 */
	X19 = 19, /* 0x98 */
	X20 = 20, /* 0xa0 */
	X21 = 21, /* 0xa8 */
	X22 = 22, /* 0xb0 */
	X23 = 23, /* 0xb8 */
	X24 = 24, /* 0xc0 */
	X25 = 25, /* 0xc8 */
	X26 = 26, /* 0xd0 */
	X27 = 27, /* 0xd8 */
	X28 = 28, /* 0xe0 */
	X29 = 29, /* 0xe8 */
	X30 = 30, /* 0xf0 */
	LR = 30,
	/* End of GP registers, the following are additional kernel-saved state. */
	SP_EL0 = 31,   /* 0xf8 */
	ELR_EL1 = 32,  /* 0x100 */
	NextIP = 32,   /* LR_svc */
	SPSR_EL1 = 33, /* 0x108 */
	FaultIP = 34,  /* 0x110 */
	/* user readable/writable thread ID register.
	 * name comes from the ARM manual */
	TPIDR_EL0 = 35,
	TLS_BASE = TPIDR_EL0,
	/* user readonly thread ID register. */
	TPIDRRO_EL0 = 36,
	n_contextRegisters = 37,
};
_Static_assert(SP_EL0 * sizeof(word_t) == (31 * 8), "sp_offset_correct");
_Static_assert(ELR_EL1 * sizeof(word_t) == (32 * 8), "lr_svc_offset_correct");
_Static_assert(FaultIP * sizeof(word_t) == (34 * 8), "faultinstruction_offset_correct");
typedef word_t register_t;
enum messageSizes {
	n_msgRegisters = 4,
	n_frameRegisters = 17,
	n_gpRegisters = 19,
	n_exceptionMessage = 3,
	n_syscallMessage = 12,
};
extern const register_t msgRegisters[];
extern const register_t frameRegisters[];
extern const register_t gpRegisters[];
typedef struct user_fpu_state {
	uint64_t vregs[64];
	uint32_t fpsr;
	uint32_t fpcr;
} user_fpu_state_t;
/* ARM user-code context: size = 72 bytes
 * Or with hardware debug support built in:
 *      72 + sizeof(word_t) * (NUM_BPS + NUM_WPS) * 2
 *
 * The "word_t registers" member of this struct must come first, because in
 * head.S, we assume that an "ldr %0, =ksCurThread" will point to the beginning
 * of the current thread's registers. The assert below should help.
 */
struct user_context {
	word_t registers[n_contextRegisters];
	user_fpu_state_t fpuState;
};
typedef struct user_context user_context_t;
_Static_assert(__builtin_offsetof(user_context_t, registers) == 0,
	       "registers_are_first_member_of_user_context");
static inline void Arch_initContext(user_context_t *context)
{
	context->registers[SPSR_EL1] = ((1 << 6) | 0 | 0);
}
typedef struct arch_tcb {
	user_context_t tcbContext;
} arch_tcb_t;
enum vm_rights { VMKernelOnly = 0, VMReadWrite = 1, VMKernelReadOnly = 2, VMReadOnly = 3 };
typedef word_t vm_rights_t;
/* If hypervisor support for aarch64 is enabled and we run on processors with
 * 40-bit PA, the stage-2 translation for EL1/EL0 uses a 3-level translation, skipping the PGD
 * level. Yet the kernel will still use a stage-1 translation with 48 bit input addresses and a
 * 4-level translation.  Therefore, PUD and PGD size for the kernel can be different from EL1/EL0 so
 * we do not use the libsel4 definitions */
/* Otherwise we use a 4-level translation */
typedef pgde_t vspace_root_t;
/* Generate a vcpu_t pointer from a vcpu block reference */
struct asid_pool {
	asid_map_t array[(1ul << (asidLowBits))];
};
typedef struct asid_pool asid_pool_t;
static inline word_t cap_get_archCapSizeBits(cap_t cap)
{
	cap_tag_t ctag;
	ctag = cap_get_capType(cap);
	switch (ctag) {
	case cap_frame_cap:
		return pageBitsForSize(cap_frame_cap_get_capFSize(cap));
	case cap_page_table_cap:
		return 12;
	case cap_page_directory_cap:
		return 12;
	case cap_page_upper_directory_cap:
		return 12;
	case cap_page_global_directory_cap:
		return 12;
	case cap_asid_pool_cap:
		return 12;
	case cap_asid_control_cap:
		return 0;
	default:
		/* Unreachable, but GCC can't figure that out */
		return 0;
	}
}
static inline bool_t cap_get_archCapIsPhysical(cap_t cap)
{
	cap_tag_t ctag;
	ctag = cap_get_capType(cap);
	switch (ctag) {
	case cap_frame_cap:
		return true;
	case cap_page_table_cap:
		return true;
	case cap_page_directory_cap:
		return true;
	case cap_page_upper_directory_cap:
		return true;
	case cap_page_global_directory_cap:
		return true;
	case cap_asid_pool_cap:
		return true;
	case cap_asid_control_cap:
		return false;
	default:
		/* Unreachable, but GCC can't figure that out */
		return false;
	}
}
static inline void *cap_get_archCapPtr(cap_t cap)
{
	cap_tag_t ctag;
	ctag = cap_get_capType(cap);
	switch (ctag) {
	case cap_frame_cap:
		return (void *)(cap_frame_cap_get_capFBasePtr(cap));
	case cap_page_table_cap:
		return ((pde_t *)(cap_page_table_cap_get_capPTBasePtr(cap)));
	case cap_page_directory_cap:
		return ((pte_t *)(cap_page_directory_cap_get_capPDBasePtr(cap)));
	case cap_page_upper_directory_cap:
		return ((pude_t *)(cap_page_upper_directory_cap_get_capPUDBasePtr(cap)));
	case cap_page_global_directory_cap:
		return ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(cap)));
	case cap_asid_control_cap:
		return NULL;
	case cap_asid_pool_cap:
		return ((asid_pool_t *)cap_asid_pool_cap_get_capASIDPool(cap));
	default:
		/* Unreachable, but GCC can't figure that out */
		return NULL;
	}
}
static inline bool_t pgde_pgde_pud_ptr_get_present(pgde_t *pgd)
{
	return (pgde_ptr_get_pgde_type(pgd) == pgde_pgde_pud);
}
static inline bool_t pude_pude_pd_ptr_get_present(pude_t *pud)
{
	return (pude_ptr_get_pude_type(pud) == pude_pude_pd);
}
static inline bool_t pude_pude_1g_ptr_get_present(pude_t *pud)
{
	return (pude_ptr_get_pude_type(pud) == pude_pude_1g);
}
static inline pude_t pude_invalid_new(void)
{
	return (pude_t){{0}};
}
static inline bool_t pde_pde_small_ptr_get_present(pde_t *pd)
{
	return (pde_ptr_get_pde_type(pd) == pde_pde_small);
}
static inline bool_t pde_pde_large_ptr_get_present(pde_t *pd)
{
	return (pde_ptr_get_pde_type(pd) == pde_pde_large);
}
static inline pde_t pde_invalid_new(void)
{
	return (pde_t){{0}};
}
static inline bool_t pte_ptr_get_present(pte_t *pt)
{
	return (pte_ptr_get_reserved(pt) == 0x3);
}
static inline pte_t pte_invalid_new(void)
{
	return (pte_t){{0}};
}
static inline bool_t Arch_isCapRevocable(cap_t derivedCap, cap_t srcCap)
{
	return false;
}
struct user_data {
	word_t words[(1ul << (12)) / sizeof(word_t)];
};
typedef struct user_data user_data_t;
struct user_data_device {
	word_t words[(1ul << (12)) / sizeof(word_t)];
};
typedef struct user_data_device user_data_device_t;
static inline word_t wordFromVMRights(vm_rights_t vm_rights)
{
	return (word_t)vm_rights;
}
static inline vm_rights_t vmRightsFromWord(word_t w)
{
	return (vm_rights_t)w;
}
static inline vm_attributes_t vmAttributesFromWord(word_t w)
{
	vm_attributes_t attr;
	attr.words[0] = w;
	return attr;
}
/* TCB: size >= 18 words + sizeof(arch_tcb_t) + 1 word on MCS (aligned to nearest power of 2) */
struct tcb {
	/* arch specific tcb state (including context)*/
	arch_tcb_t tcbArch;
	/* Thread state, 3 words */
	thread_state_t tcbState;
	/* Notification that this TCB is bound to. If this is set, when this TCB waits on
	 * any sync endpoint, it may receive a signal from a Notification object.
	 * 1 word*/
	notification_t *tcbBoundNotification;
	/* Current fault, 2 words */
	seL4_Fault_t tcbFault;
	/* Current lookup failure, 2 words */
	lookup_fault_t tcbLookupFailure;
	/* Domain, 1 byte (padded to 1 word) */
	dom_t tcbDomain;
	/*  maximum controlled priority, 1 byte (padded to 1 word) */
	prio_t tcbMCP;
	/* Priority, 1 byte (padded to 1 word) */
	prio_t tcbPriority;
	/* Timeslice remaining, 1 word */
	word_t tcbTimeSlice;
	/* Capability pointer to thread fault handler, 1 word */
	cptr_t tcbFaultHandler;
	/* userland virtual address of thread IPC buffer, 1 word */
	word_t tcbIPCBuffer;
	/* Previous and next pointers for scheduler queues , 2 words */
	struct tcb *tcbSchedNext;
	struct tcb *tcbSchedPrev;
	/* Preivous and next pointers for endpoint and notification queues, 2 words */
	struct tcb *tcbEPNext;
	struct tcb *tcbEPPrev;
};
typedef struct tcb tcb_t;
/* This debug_tcb object is inserted into the 'unused' region of a TCB object
   for debug build configurations. */
struct debug_tcb {
	/* Pointers for list of all tcbs that is maintained
	 * when CONFIG_DEBUG_BUILD is enabled, 2 words */
	struct tcb *tcbDebugNext;
	struct tcb *tcbDebugPrev;
	/* Use any remaining space for a thread name */
	char tcbName[];
};
typedef struct debug_tcb debug_tcb_t;
/* Ensure object sizes are sane */
_Static_assert(sizeof(cte_t) <= (1ul << (5)), "cte_size_sane");
_Static_assert((4 + 5) <= (11 - 1), "tcb_cte_size_sane");
_Static_assert((1ul << ((11 - 1))) >= sizeof(tcb_t), "tcb_size_sane");
_Static_assert((1ul << ((11 - 1) - 1)) < sizeof(tcb_t), "tcb_size_not_excessive");
_Static_assert(sizeof(endpoint_t) <= (1ul << (4)), "ep_size_sane");
_Static_assert(sizeof(notification_t) <= (1ul << (5)), "notification_size_sane");
/* Check the IPC buffer is the right size */
_Static_assert(sizeof(seL4_IPCBuffer) == (1ul << (10)), "ipc_buf_size_sane");
/* helper functions */
static inline word_t isArchCap(cap_t cap)
{
	return (cap_get_capType(cap) % 2);
}
struct pde_range {
	pde_t *base;
	word_t length;
};
typedef struct pde_range pde_range_t;
struct pte_range {
	pte_t *base;
	word_t length;
};
typedef struct pte_range pte_range_t;
typedef cte_t *cte_ptr_t;
struct extra_caps {
	cte_ptr_t excaprefs[((1ul << (seL4_MsgExtraCapBits)) - 1)];
};
typedef struct extra_caps extra_caps_t;
word_t setMRs_fault(tcb_t *sender, tcb_t *receiver, word_t *receiveIPCBuffer);
word_t Arch_setMRs_fault(tcb_t *sender, tcb_t *receiver, word_t *receiveIPCBuffer,
			 word_t faultType);
bool_t handleFaultReply(tcb_t *receiver, tcb_t *sender);
bool_t Arch_handleFaultReply(tcb_t *receiver, tcb_t *sender, word_t faultType);
/*
 * This file is autogenerated by <kernel>/tools/hardware/outputs/c_header.py.
 */
/* EL2 kernel address map:
 *
 * The EL2 mode kernel uses TTBR0_EL2 which covers the range of
 * 0x0 - 0x0000ffffffffffff (48 bits of vaddrspace).
 *
 * The CPU on the TX1 only allows for 48-bits of addressable virtual memory.
 * Within the seL4 EL2 kernel's separate vaddrspace, it uses
 * the 512 GiB at the top of that 48 bits of addressable
 * virtual memory.
 *
 * In EL2 there is no canonical-high portion of the address space since
 * address tagging is not supported in EL2. Therefore the kernel is linked
 * to the canonical lower portion of the address space (all the unused top bits
 * are set to 0, not 1).
 *
 * The memory map used by the EL2 kernel's separate address space
 * ends up looking something like this:
 *
 * +-----------------------------------+ <- 0xFFFFFFFF_FFFFFFFF
 * | Canonical high portion - unusable |
 * | virtual addrs                     |
 * +-----------------------------------+ <- PPTR_TOP: 256TiB mark (top of 48 bits)
 * | seL4 EL2 kernel                   |    ^
 * |                                   |    |
 * |                                   |    512GiB
 * |                                   |    of EL2 kernel windowing
 * |                                   |    into memory.
 * |                                   |    |
 * |                                   |    v
 * +-----------------------------------+ <- PPTR_BASE: 256TiB minus 512GiB.
 * | Unused virtual addresses within   |    ^
 * | the EL2 kernel's                  |    |
 * | separate vaddrspace.              |    Rest of the
 * |                                   |    EL2 kernel
 * |                                   |    vaddrspace, unused,
 * |                                   |    which is the rest of
 * |                                   |    the lower 256 TiB.
 * |                                   |    |
 * |                                   |    v
 * +-----------------------------------+ <- 0x0
 *
 * !defined(CONFIG_ARM_HYPERVISOR_SUPPORT)
 *
 *          2^64 +-------------------+
 *               | Kernel Page PDPT  | --------------+
 *   2^64 - 2^39 +-------------------+ PPTR_BASE     |
 *               |    TLB Bitmaps    |               |
 *               +-------------------+               |
 *               |                   |               |
 *               |     Unmapped      |               |
 *               |                   |               |
 *   2^64 - 2^48 +-------------------+               |
 *               |                   |               |
 *               |   Unaddressable   |               |
 *               |                   |               |
 *          2^48 +-------------------+ USER_TOP      |
 *               |                   |               |
 *               |       User        |               |
 *               |                   |               |
 *           0x0 +-------------------+               |
 *                                                   |
 *                         +-------------------------+
 *                         |
 *                         v
 *          2^64 +-------------------+
 *               |                   |
 *               |                   |     +------+
 *               | Kernel Page Table | --> |  PD  | ----+
 *               |                   |     +------+     |
 *               |                   |                  |
 *   2^64 - 2^30 +-------------------+ PPTR_TOP         |
 *               |                   |                  |
 *               |  Physical Memory  |                  |
 *               |       Window      |                  |
 *               |                   |                  |
 *               +-------------------+                  |
 *               |                   |                  |
 *               |                   |     +------+     |
 *               |    Kernel ELF     | --> |  PD  |     |
 *               |                   |     +------+     |
 *               |                   |                  |
 *               +-------------------+ KERNEL_ELF_BASE  |
 *               |                   |                  |
 *               |  Physical Memory  |                  |
 *               |       Window      |                  |
 *               |                   |                  |
 *   2^64 - 2^39 +-------------------+ PPTR_BASE        |
 *                                                      |
 *                                +---------------------+
 *                                |
 *                                v
 *   2^64 - 2^21 + 2^12 +-------------------+
 *                      |                   |
 *                      |  Kernel Devices   |
 *                      |                   |
 *          2^64 - 2^21 +-------------------+ KDEV_BASE
 *
 *
/* last accessible virtual address in user space */
/* The first physical address to map into the kernel's physical memory
 * window */
/* The base address in virtual memory to use for the 1:1 physical memory
 * mapping */
/* Top of the physical memory window */
/* The physical memory address to use for mapping the kernel ELF */
/* The base address in virtual memory to use for the kernel ELF mapping */
/* This is a page table mapping at the end of the virtual address space
 * to map objects with 4KiB pages rather than 4MiB large pages. */
/* The base address in virtual memory to use for the kernel device
 * mapping region. These are mapped in the kernel page table. */
/* The log buffer is placed before the device region */
/* All PPTR addresses must be canonical to be able to be stored in caps or objects.
   Check that all UTs that are created will have valid address in the PPTR space.
   For non-hyp, PPTR_BASE is in the top part of the address space and device untyped
   addresses are allowed to be large enough to overflow and be in the bottom half of
   the address space.  However, when the kernel is in EL2 it is not possible to safely
   overflow without going into address ranges that are non-canonical.  These static
   asserts check that the kernel config won't lead to UTs being created that aren't
   representable. */
_Static_assert(1099511627776 <= (1ul << (47)), "ut_max_less_than_cannonical");
;
/* Place-holder for ARM-related linker definitions */
/* code that is only used during kernel bootstrapping */
/* read-only data only used during kernel bootstrapping */
/* read/write data only used during kernel bootstrapping */
/* node-local bss data that is only used during kernel bootstrapping */
/* data will be aligned to n bytes in a special BSS section */
/* data that will be mapped into and permitted to be used in the restricted SKIM
 * address space */
/* bss data that is permitted to be used in the restricted SKIM address space */
/* INTERRUPTS */
/* INTERRUPT_VTIMER_EVENT generated from /timer */
/* KERNEL_TIMER_IRQ generated from /timer */
/* KERNEL DEVICES */
static const kernel_frame_t kernel_device_frames[] = {
	/* /pl011@9000000 */
	{.paddr = 0x9000000, .pptr = UART_PPTR, .armExecuteNever = true, .userAvailable = true},
	/* /intc@8000000 */
	{.paddr = 0x8000000,
	 .pptr = GIC_V2_DISTRIBUTOR_PPTR,
	 .armExecuteNever = true,
	 .userAvailable = false},
	/* /intc@8000000 */
	{.paddr = 0x8010000,
	 .pptr = GIC_V2_CONTROLLER_PPTR,
	 .armExecuteNever = true,
	 .userAvailable = false}

};

/* Elements in kernel_device_frames may be enabled in specific configurations
 * only, but the ARRAY_SIZE() macro will automatically take care of this.
 * However, one corner case remains unsolved where all elements are disabled
 * and this becomes an empty array effectively. Then the C parser used in the
 * formal verification process will fail, because it follows the strict C rules
 * which do not allow empty arrays. Luckily, we have not met this case yet...
 */
/* PHYSICAL MEMORY */
static const p_region_t avail_p_regs[] = {
	/* /memory@40000000 */
	{.start = 0x40000000, .end = 0x80000000},
};
enum IRQConstants { maxIRQ = 159 } platform_interrupt_t;
/*
 * ARM Generic Interrupt Controller PL-390
 */
/* tell the kernel we have the set trigger feature */
/* These are the stacks used in kernel, shared between architectures/modes.
 * CONFIG_KERNEL_STACK_BITS is defined in kernel/Kconfig. The physical/offset
 * address of the stack is per-arch-mode aligned. KERNEL_STACK_ALIGNMENT is
 * defined for each arch/mode in <mode/kernel/stack.h>
 */
extern char kernel_stack_alloc[1][(1ul << (12))];
typedef enum {
	seL4_NoError = 0,
	seL4_InvalidArgument,
	seL4_InvalidCapability,
	seL4_IllegalOperation,
	seL4_RangeError,
	seL4_AlignmentError,
	seL4_FailedLookup,
	seL4_TruncatedMessage,
	seL4_DeleteFirst,
	seL4_RevokeFirst,
	seL4_NotEnoughMemory,
	/* This should always be the last item in the list
	 * so it gives a count of the number of errors in the
	 * enum.
	 */
	seL4_NumErrors
} seL4_Error;
/* These datatypes differ markedly from haskell, due to the
 * different implementation of the various fault monads */
enum exception {
	EXCEPTION_NONE,
	EXCEPTION_FAULT,
	EXCEPTION_LOOKUP_FAULT,
	EXCEPTION_SYSCALL_ERROR,
	EXCEPTION_PREEMPTED
};
typedef word_t exception_t;
typedef word_t syscall_error_type_t;
struct syscall_error {
	word_t invalidArgumentNumber;
	word_t invalidCapNumber;
	word_t rangeErrorMin;
	word_t rangeErrorMax;
	word_t memoryLeft;
	bool_t failedLookupWasSource;
	syscall_error_type_t type;
};
typedef struct syscall_error syscall_error_t;
extern lookup_fault_t current_lookup_fault;
extern seL4_Fault_t current_fault;
extern syscall_error_t current_syscall_error;
typedef enum {
	MessageID_Syscall,
	MessageID_Exception,
} MessageID_t;
extern const register_t fault_messages[][(
	((n_syscallMessage) > (n_exceptionMessage)) ? (n_syscallMessage) : (n_exceptionMessage))];
static inline void setRegister(tcb_t *thread, register_t reg, word_t w)
{
	thread->tcbArch.tcbContext.registers[reg] = w;
}
static inline word_t getRegister(tcb_t *thread, register_t reg)
{
	return thread->tcbArch.tcbContext.registers[reg];
}
exception_t decodeCNodeInvocation(word_t invLabel, word_t length, cap_t cap, word_t *buffer);
exception_t invokeCNodeRevoke(cte_t *destSlot);
exception_t invokeCNodeDelete(cte_t *destSlot);
exception_t invokeCNodeCancelBadgedSends(cap_t cap);
exception_t invokeCNodeInsert(cap_t cap, cte_t *srcSlot, cte_t *destSlot);
exception_t invokeCNodeMove(cap_t cap, cte_t *srcSlot, cte_t *destSlot);
exception_t invokeCNodeRotate(cap_t cap1, cap_t cap2, cte_t *slot1, cte_t *slot2, cte_t *slot3);
void cteInsert(cap_t newCap, cte_t *srcSlot, cte_t *destSlot);
void cteMove(cap_t newCap, cte_t *srcSlot, cte_t *destSlot);
void capSwapForDelete(cte_t *slot1, cte_t *slot2);
void cteSwap(cap_t cap1, cte_t *slot1, cap_t cap2, cte_t *slot2);
exception_t cteRevoke(cte_t *slot);
exception_t cteDelete(cte_t *slot, bool_t exposed);
void cteDeleteOne(cte_t *slot);
void insertNewCap(cte_t *parent, cte_t *slot, cap_t cap);
bool_t isMDBParentOf(cte_t *cte_a, cte_t *cte_b);
exception_t ensureNoChildren(cte_t *slot);
exception_t ensureEmptySlot(cte_t *slot);
bool_t isFinalCapability(cte_t *cte);
bool_t slotCapLongRunningDelete(cte_t *slot);
cte_t *getReceiveSlots(tcb_t *thread, word_t *buffer);
cap_transfer_t loadCapTransfer(word_t *buffer);
exception_t invokeCNodeSaveCaller(cte_t *destSlot);
void setupReplyMaster(tcb_t *thread);
/* Maximum length of the tcb name, including null terminator */
_Static_assert(((1ul << (11 - 1)) - (tcbCNodeEntries * sizeof(cte_t)) - sizeof(debug_tcb_t)) > 0,
	       "tcb_name_fits");
struct tcb_queue {
	tcb_t *head;
	tcb_t *end;
};
typedef struct tcb_queue tcb_queue_t;
static inline unsigned int setMR(tcb_t *receiver, word_t *receiveIPCBuffer, unsigned int offset,
				 word_t reg)
{
	if (offset >= n_msgRegisters) {
		if (receiveIPCBuffer) {
			receiveIPCBuffer[offset + 1] = reg;
			return offset + 1;
		} else {
			return n_msgRegisters;
		}
	} else {
		setRegister(receiver, msgRegisters[offset], reg);
		return offset + 1;
	}
}
void tcbSchedEnqueue(tcb_t *tcb);
void tcbSchedAppend(tcb_t *tcb);
void tcbSchedDequeue(tcb_t *tcb);
void tcbDebugAppend(tcb_t *tcb);
void tcbDebugRemove(tcb_t *tcb);
tcb_queue_t tcbEPAppend(tcb_t *tcb, tcb_queue_t queue);
tcb_queue_t tcbEPDequeue(tcb_t *tcb, tcb_queue_t queue);
void setupCallerCap(tcb_t *sender, tcb_t *receiver, bool_t canGrant);
void deleteCallerCap(tcb_t *receiver);
word_t copyMRs(tcb_t *sender, word_t *sendBuf, tcb_t *receiver, word_t *recvBuf, word_t n);
exception_t decodeTCBInvocation(word_t invLabel, word_t length, cap_t cap, cte_t *slot, bool_t call,
				word_t *buffer);
exception_t decodeCopyRegisters(cap_t cap, word_t length, word_t *buffer);
exception_t decodeReadRegisters(cap_t cap, word_t length, bool_t call, word_t *buffer);
exception_t decodeWriteRegisters(cap_t cap, word_t length, word_t *buffer);
exception_t decodeTCBConfigure(cap_t cap, word_t length, cte_t *slot, word_t *buffer);
exception_t decodeSetPriority(cap_t cap, word_t length, word_t *buffer);
exception_t decodeSetMCPriority(cap_t cap, word_t length, word_t *buffer);
exception_t decodeSetSchedParams(cap_t cap, word_t length, word_t *buffer);
exception_t decodeSetIPCBuffer(cap_t cap, word_t length, cte_t *slot, word_t *buffer);
exception_t decodeSetSpace(cap_t cap, word_t length, cte_t *slot, word_t *buffer);
exception_t decodeDomainInvocation(word_t invLabel, word_t length, word_t *buffer);
exception_t decodeBindNotification(cap_t cap);
exception_t decodeUnbindNotification(cap_t cap);
enum thread_control_flag {
	thread_control_update_priority = 0x1,
	thread_control_update_ipc_buffer = 0x2,
	thread_control_update_space = 0x4,
	thread_control_update_mcp = 0x8,
};
typedef word_t thread_control_flag_t;
exception_t invokeTCB_Suspend(tcb_t *thread);
exception_t invokeTCB_Resume(tcb_t *thread);
exception_t invokeTCB_ThreadControl(tcb_t *target, cte_t *slot, cptr_t faultep, prio_t mcp,
				    prio_t priority, cap_t cRoot_newCap, cte_t *cRoot_srcSlot,
				    cap_t vRoot_newCap, cte_t *vRoot_srcSlot, word_t bufferAddr,
				    cap_t bufferCap, cte_t *bufferSrcSlot,
				    thread_control_flag_t updateFlags);
exception_t invokeTCB_CopyRegisters(tcb_t *dest, tcb_t *src, bool_t suspendSource,
				    bool_t resumeTarget, bool_t transferFrame,
				    bool_t transferInteger, word_t transferArch);
exception_t invokeTCB_ReadRegisters(tcb_t *src, bool_t suspendSource, word_t n, word_t arch,
				    bool_t call);
exception_t invokeTCB_WriteRegisters(tcb_t *dest, bool_t resumeTarget, word_t n, word_t arch,
				     word_t *buffer);
exception_t invokeTCB_NotificationControl(tcb_t *tcb, notification_t *ntfnPtr);
cptr_t getExtraCPtr(word_t *bufferPtr, word_t i);
void setExtraBadge(word_t *bufferPtr, word_t badge, word_t i);
exception_t lookupExtraCaps(tcb_t *thread, word_t *bufferPtr, seL4_MessageInfo_t info);
word_t setMRs_syscall_error(tcb_t *thread, word_t *receiveIPCBuffer);
word_t Arch_decodeTransfer(word_t flags);
exception_t Arch_performTransfer(word_t arch, tcb_t *tcb_src, tcb_t *tcb_dest);
void setThreadName(tcb_t *thread, const char *name);
/* UP states are declared as VISIBLE so that they are accessible in assembly */
extern tcb_queue_t ksReadyQueues[(1 * 256)];
extern word_t ksReadyQueuesL1Bitmap[1];
extern word_t ksReadyQueuesL2Bitmap[1][((256 + (1 << 6) - 1) / (1 << 6))];
extern tcb_t *ksCurThread;
extern tcb_t *ksIdleThread;
extern tcb_t *ksSchedulerAction;
/* Current state installed in the FPU, or NULL if the FPU is currently invalid */
extern user_fpu_state_t *ksActiveFPUState;
/* Number of times we have restored a user context with an active FPU without switching it */
extern word_t ksFPURestoresSinceSwitch;
extern tcb_t *ksDebugTCBs;
;
extern word_t ksNumCPUs;
extern word_t ksWorkUnitsCompleted;
extern irq_state_t intStateIRQTable[];
extern cte_t intStateIRQNode[];
extern const dschedule_t ksDomSchedule[];
extern const word_t ksDomScheduleLength;
extern word_t ksDomScheduleIdx;
extern dom_t ksCurDomain;
extern word_t ksDomainTime;
extern word_t tlbLockCount;
extern char ksIdleThreadTCB[1][(1ul << (11))];
/**
 * irq_t is an identifier that represents a hardware interrupt.
 * irq handler capabilities refer to an irq_t which is then used by the
 * kernel to track irq state. An irq_t is also used to interface with an
 * interrupt controller driver using the functions below.
 * For most configurations an irq_t is a word_t type and the irq_t values
 * directly map to harware irq numbers and are also used as indexes into the
 * kernel's irq cnode that it uses for tracking state.
 * However on SMP configurations where there can be multiple irq_t identifiers
 * for a single hardware irq number, such as when there are core local interrupts,
 * irq_t cannot be assumed to be only a hardware irq number.
 * In this case, irq_t can be defined as a struct containing additional information.
 *
 * Macros are provided to hide this structural difference across configurations:
 * CORE_IRQ_TO_IRQT: converts from a core id and hw irq number to an irq_t
 * IRQT_TO_IDX: converts an irq_t to an index in the irq cnode. It is also used
 *   to encode the irq_t as a single word_t type for sending over IPIs.
 * IDX_TO_IRQT: converts an index in the irq cnode to an irq_t
 * IRQT_TO_CORE: extracts the core out of an irq_t
 * IRQT_TO_IRQL extracts a hw irq out of an irq_t.
 *
 * It is expected that interrupt controller drivers that support SMP provide
 * implementations of these Macros.
 * Currently only Arm SMP configurations use this scheme.
 */
typedef word_t irq_t;
/**
 * Return a currently pending IRQ.
 *
 * This function can be called multiple times and needs to return the same IRQ
 * until ackInterrupt is called. getActiveIRQ returns irqInvalid if no interrupt
 * is pending. It is assumed that if isIRQPending is true, then getActiveIRQ
 * will not return irqInvalid. irqInvalid is a per platform constant that cannot
 * correspond to an actual IRQ raised by the platform.
 *
 * @return     The active IRQ. irqInvalid if no IRQ is pending.
 */
static inline irq_t getActiveIRQ(void);
/**
 * Checks if an IRQ is currently pending in the hardware.
 *
 * isIRQPending is used to determine whether to preempt long running operations
 * at various preemption points throughout the kernel. If this returns true, it
 * means that if the Kernel were to return to user mode, it would then
 * immediately take an interrupt.
 *
 * @return     True if irq pending, False otherwise.
 */
static inline bool_t isIRQPending(void);
/**
 * maskInterrupt disables and enables IRQs.
 *
 * When an IRQ is disabled, it should not raise an interrupt on the processor.
 *
 * @param[in]  disable  True to disable IRQ, False to enable IRQ
 * @param[in]  irq      The irq to modify
 */
static inline void maskInterrupt(bool_t disable, irq_t irq);
/**
 * Acks the interrupt
 *
 * ackInterrupt is used by the kernel to indicate it has processed the interrupt
 * delivery and getActiveIRQ is now able to return a different IRQ number. Note
 * that this is called after a notification has been signalled to user level,
 * but before user level has handled the cause and does not imply that the cause
 * of the interrupt has been handled.
 *
 * @param[in]  irq   irq to ack
 */
static inline void ackInterrupt(irq_t irq);
/**
 * Called when getActiveIRQ returns irqInvalid while the kernel is handling an
 * interrupt entry. An implementation is not required to do anything here, but
 * can report the spurious IRQ or try prevent it from reoccuring.
 */
static inline void handleSpuriousIRQ(void);
/**
 * Handle a platform-reserved IRQ.
 *
 * Platform specific implementation for handling IRQs for interrupts that are
 * reserved and not made available to user-level. Will be called if getActiveIRQ
 * returns an IRQ number that is reserved. After this function returns,
 * ackInterrupt will likely be immediately called after.
 *
 * @param[in]  irq   The irq
 */
static inline void handleReservedIRQ(irq_t irq);
/* Shift positions for GICD_SGIR register */
/* Special IRQ's */
/* CPU specific IRQ's */
/* Shared Peripheral Interrupts */
irq_t irqInvalid = (uint16_t)-1;
/* Setters/getters helpers for hardware irqs */
/*
 * The only sane way to get an GIC IRQ number that can be properly
 * ACKED later is through the int_ack register. Unfortunately, reading
 * this register changes the interrupt state to pending so future
 * reads will not return the same value For this reason, we have a
 * global variable to store the IRQ number.
 */
extern word_t active_irq[1];
static inline void handleSpuriousIRQ(void) {}
void initIRQController(void);
/* Helpers for VGIC */
/* Memory map for GIC distributor */
struct gic_dist_map {
	uint32_t enable;	     /* 0x000 */
	uint32_t ic_type;	     /* 0x004 */
	uint32_t dist_ident;	     /* 0x008 */
	uint32_t res1[29];	     /* [0x00C, 0x080) */
	uint32_t security[32];	     /* [0x080, 0x100) */
	uint32_t enable_set[32];     /* [0x100, 0x180) */
	uint32_t enable_clr[32];     /* [0x180, 0x200) */
	uint32_t pending_set[32];    /* [0x200, 0x280) */
	uint32_t pending_clr[32];    /* [0x280, 0x300) */
	uint32_t active[32];	     /* [0x300, 0x380) */
	uint32_t res2[32];	     /* [0x380, 0x400) */
	uint32_t priority[255];	     /* [0x400, 0x7FC) */
	uint32_t res3;		     /* 0x7FC */
	uint32_t targets[255];	     /* [0x800, 0xBFC) */
	uint32_t res4;		     /* 0xBFC */
	uint32_t config[64];	     /* [0xC00, 0xD00) */
	uint32_t spi[32];	     /* [0xD00, 0xD80) */
	uint32_t res5[20];	     /* [0xD80, 0xDD0) */
	uint32_t res6;		     /* 0xDD0 */
	uint32_t legacy_int;	     /* 0xDD4 */
	uint32_t res7[2];	     /* [0xDD8, 0xDE0) */
	uint32_t match_d;	     /* 0xDE0 */
	uint32_t enable_d;	     /* 0xDE4 */
	uint32_t res8[70];	     /* [0xDE8, 0xF00) */
	uint32_t sgi_control;	     /* 0xF00 */
	uint32_t res9[3];	     /* [0xF04, 0xF10) */
	uint32_t sgi_pending_clr[4]; /* [0xF10, 0xF20) */
	uint32_t res10[40];	     /* [0xF20, 0xFC0) */
	uint32_t periph_id[12];	     /* [0xFC0, 0xFF0) */
	uint32_t component_id[4];    /* [0xFF0, 0xFFF] */
};
/* Memory map for GIC  cpu interface */
struct gic_cpu_iface_map {
	uint32_t icontrol;		/*  0x000         */
	uint32_t pri_msk_c;		/*  0x004         */
	uint32_t pb_c;			/*  0x008         */
	uint32_t int_ack;		/*  0x00C         */
	uint32_t eoi;			/*  0x010         */
	uint32_t run_priority;		/*  0x014         */
	uint32_t hi_pend;		/*  0x018         */
	uint32_t ns_alias_bp_c;		/*  0x01C         */
	uint32_t ns_alias_ack;		/*  0x020 GIC400 only */
	uint32_t ns_alias_eoi;		/*  0x024 GIC400 only */
	uint32_t ns_alias_hi_pend;	/*  0x028 GIC400 only */
	uint32_t res1[5];		/* [0x02C, 0x040) */
	uint32_t integ_en_c;		/*  0x040 PL390 only */
	uint32_t interrupt_out;		/*  0x044 PL390 only */
	uint32_t res2[2];		/* [0x048, 0x050)    */
	uint32_t match_c;		/*  0x050 PL390 only */
	uint32_t enable_c;		/*  0x054 PL390 only */
	uint32_t res3[30];		/* [0x058, 0x0FC)  */
	uint32_t active_priority[4];	/* [0x0D0, 0xDC] GIC400 only */
	uint32_t ns_active_priority[4]; /* [0xE0,0xEC] GIC400 only */
	uint32_t res4[3];
	uint32_t cpu_if_ident;	  /*  0x0FC         */
	uint32_t res5[948];	  /* [0x100. 0xFC0) */
	uint32_t periph_id[8];	  /* [0xFC0, 9xFF0) PL390 only */
	uint32_t component_id[4]; /* [0xFF0, 0xFFF] PL390 only */
};
extern volatile struct gic_dist_map *const gic_dist;
extern volatile struct gic_cpu_iface_map *const gic_cpuiface;
/* Helpers */
static inline int is_irq_edge_triggered(word_t irq)
{
	int word = irq >> 4;
	int bit = ((irq & 0xf) * 2);
	return !!(gic_dist->config[word] & (1ul << (bit + 1)));
}
static inline void dist_pending_clr(word_t irq)
{
	int word = ((irq) >> 5u);
	int bit = ((irq)&0x1f);
	/* Using |= here is detrimental to your health */
	gic_dist->pending_clr[word] = (1ul << (bit));
}
static inline void dist_enable_clr(word_t irq)
{
	int word = ((irq) >> 5u);
	int bit = ((irq)&0x1f);
	/* Using |= here is detrimental to your health */
	gic_dist->enable_clr[word] = (1ul << (bit));
}
static inline void dist_enable_set(word_t irq)
{
	int word = ((irq) >> 5u);
	int bit = ((irq)&0x1f);
	gic_dist->enable_set[word] = (1ul << (bit));
}
static inline irq_t getActiveIRQ(void)
{
	irq_t irq;
	if (!(((active_irq[0lu]) & ((1ul << (10u)) - 1ul)) < 1020u)) {
		active_irq[0lu] = gic_cpuiface->int_ack;
	}
	if ((((active_irq[0lu]) & ((1ul << (10u)) - 1ul)) < 1020u)) {
		irq = (active_irq[0lu] & ((1ul << (10u)) - 1ul));
	} else {
		irq = irqInvalid;
	}
	return irq;
}
/*
 * GIC has 4 states: pending->active(+pending)->inactive
 * seL4 expects two states: active->inactive.
 * We ignore the active state in GIC to conform
 */
static inline bool_t isIRQPending(void)
{
	return (((gic_cpuiface->hi_pend) & ((1ul << (10u)) - 1ul)) < 1020u);
}
static inline void maskInterrupt(bool_t disable, irq_t irq)
{
	if (disable) {
		dist_enable_clr((irq));
	} else {
		dist_enable_set((irq));
	}
}
static inline void ackInterrupt(irq_t irq)
{
	if (is_irq_edge_triggered((irq))) {
		dist_pending_clr((irq));
	}
	gic_cpuiface->eoi = active_irq[0lu];
	active_irq[0lu] = 1023u;
}
static inline void wfi(void)
{
	__asm__ volatile("wfi" ::: "memory");
}
static inline void dsb(void)
{
	__asm__ volatile("dsb sy" ::: "memory");
}
static inline void dmb(void)
{
	__asm__ volatile("dmb sy" ::: "memory");
}
static inline void isb(void)
{
	__asm__ volatile("isb sy" ::: "memory");
}
/* used in boot.c with a guard, use a marco to avoid exposing vcpu_t */
static inline void VGICMaintenance(void) {}
/* These are used to force specific outcomes for various combinations of
 * settings for the state of CONFIG_ARM_HYPERVISOR_SUPPORT,
 * CONFIG_ARM_HYP_ENABLE_VCPU_CP14_SAVE_AND_RESTORE and
 * CONFIG_HARDWARE_DEBUG_API.
 */
/* TODO: add ARM-dependent fields here */
/* Bitmask of all cores should receive the reschedule IPI */
extern word_t ipiReschedulePending;
;
static inline void writeTPIDR_EL2(word_t reg) {}
static inline word_t readTPIDR_EL2(void)
{
	return 0;
}
/* used in other files without guards */
static inline void setCurrentPDPL2(paddr_t pa) {}
static inline void invalidateHypTLB(void) {}
static inline void writeContextIDPL2(word_t pd_val) {}
static inline void writeContextIDAndPD(word_t id, word_t pd_val) {}
static inline paddr_t addressTranslateS1CPR(vptr_t vaddr)
{
	return vaddr;
}
word_t getRestartPC(tcb_t *thread);
void setNextPC(tcb_t *thread, word_t v);
static inline word_t getProcessorID(void)
{
	word_t processor_id;
	__asm__ volatile("mrs %x0,"
			 "midr_el1"
			 : "=r"(processor_id));
	return processor_id;
}
static inline word_t readSystemControlRegister(void)
{
	word_t scr;
	__asm__ volatile("mrs %x0,"
			 "sctlr_el1"
			 : "=r"(scr));
	return scr;
}
static inline void writeSystemControlRegister(word_t scr)
{
	do {
		word_t _v = scr;
		__asm__ volatile("msr "
				 "sctlr_el1"
				 ",%x0" ::"r"(_v));
	} while (0);
}
static inline word_t readAuxiliaryControlRegister(void)
{
	word_t acr;
	__asm__ volatile("mrs %x0,"
			 "actlr_el1"
			 : "=r"(acr));
	return acr;
}
static inline void writeAuxiliaryControlRegister(word_t acr)
{
	do {
		word_t _v = acr;
		__asm__ volatile("msr "
				 "actlr_el1"
				 ",%x0" ::"r"(_v));
	} while (0);
}
static inline void writeTPIDR_EL0(word_t reg)
{
	do {
		word_t _v = reg;
		__asm__ volatile("msr "
				 "tpidr_el0"
				 ",%x0" ::"r"(_v));
	} while (0);
}
static inline word_t readTPIDR_EL0(void)
{
	word_t reg;
	__asm__ volatile("mrs %x0,"
			 "tpidr_el0"
			 : "=r"(reg));
	return reg;
}
static inline void writeTPIDRRO_EL0(word_t reg)
{
	do {
		word_t _v = reg;
		__asm__ volatile("msr "
				 "tpidrro_el0"
				 ",%x0" ::"r"(_v));
	} while (0);
}
static inline word_t readTPIDRRO_EL0(void)
{
	word_t reg;
	__asm__ volatile("mrs %x0,"
			 "tpidrro_el0"
			 : "=r"(reg));
	return reg;
}
static inline void writeTPIDR_EL1(word_t reg)
{
	do {
		word_t _v = reg;
		__asm__ volatile("msr "
				 "tpidr_el1"
				 ",%x0" ::"r"(_v));
	} while (0);
}
static inline word_t readTPIDR_EL1(void)
{
	word_t reg;
	__asm__ volatile("mrs %x0,"
			 "tpidr_el1"
			 : "=r"(reg));
	return reg;
}
static void arm_save_thread_id(tcb_t *thread)
{
	setRegister(thread, TPIDR_EL0, readTPIDR_EL0());
	setRegister(thread, TPIDRRO_EL0, readTPIDRRO_EL0());
}
static void arm_load_thread_id(tcb_t *thread)
{
	writeTPIDR_EL0(getRegister(thread, TPIDR_EL0));
	writeTPIDRRO_EL0(getRegister(thread, TPIDRRO_EL0));
}
/* Check if the elfloader set up the TCR_EL2 correctly. */
static inline bool_t checkTCR_EL2(void)
{
	word_t tcr_el2 = 0;
	__asm__ volatile("mrs %x0,"
			 "tcr_el2"
			 : "=r"(tcr_el2));
	return (tcr_el2 == ((16) | (1ul << (8)) | (1ul << (10)) | (3 << 12) | (0 << 14) |
			    (4 << 16) | ((1ul << (23)) | (1ul << (31)))));
}
static inline void setCurrentKernelVSpaceRoot(ttbr_t ttbr)
{
	dsb();

	word_t _v = ttbr.words[0];
	__asm__ volatile("msr "
			 "ttbr1_el1"
			 ",%x0" ::"r"(_v));

	isb();
}
static inline void setCurrentUserVSpaceRoot(ttbr_t ttbr)
{
	dsb();
	word_t _v = ttbr.words[0];
	__asm__ volatile("msr "
			 "ttbr0_el1"
			 ",%x0" ::"r"(_v));
	isb();
}
static inline word_t getVTTBR(void)
{
	word_t vttbr;
	__asm__ volatile("mrs %x0,"
			 "vttbr_el2"
			 : "=r"(vttbr));
	return vttbr;
}
static inline void setKernelStack(word_t stack_address)
{
	writeTPIDR_EL1(stack_address);
}
static inline void setVtable(pptr_t addr)
{
	dsb();
	word_t _v = addr;
	__asm__ volatile("msr "
			 "vbar_el1"
			 ",%x0" ::"r"(_v));
	isb();
}
static inline void invalidateLocalTLB_EL2(void)
{
	__asm__ volatile("tlbi alle2");
}
static inline void invalidateLocalTLB_EL1(void)
{
	__asm__ volatile("tlbi alle1");
}
static inline void invalidateLocalTLB(void)
{
	dsb();
	__asm__ volatile("tlbi vmalle1");
	dsb();
	isb();
}
static inline void invalidateLocalTLB_ASID(asid_t asid)
{
	dsb();
	__asm__ volatile("tlbi aside1, %0" : : "r"(asid << 48));
	dsb();
	isb();
}
static inline void invalidateLocalTLB_VAASID(word_t mva_plus_asid)
{
	dsb();
	__asm__ volatile("tlbi vae1, %0" : : "r"(mva_plus_asid));
	dsb();
	isb();
}
/* Invalidate all stage 1 and stage 2 translations used at
 * EL1 with the current VMID which is specified by vttbr_el2 */
static inline void invalidateLocalTLB_VMALLS12E1(void)
{
	__asm__ volatile("tlbi vmalls12e1");
	dsb();
	isb();
}
/* Invalidate IPA with the current VMID */
static inline void invalidateLocalTLB_IPA(word_t ipa)
{
	__asm__ volatile("tlbi ipas2e1, %0" ::"r"(ipa));
	dsb();
	__asm__ volatile("tlbi vmalle1");
	dsb();
	isb();
}
void lockTLBEntry(vptr_t vaddr);
static inline void cleanByVA(vptr_t vaddr, paddr_t paddr)
{
	__asm__ volatile("dc cvac, %0" : : "r"(vaddr));
	dmb();
}
static inline void cleanByVA_PoU(vptr_t vaddr, paddr_t paddr)
{
	__asm__ volatile("dc cvau, %0" : : "r"(vaddr));
	dmb();
}
static inline void invalidateByVA(vptr_t vaddr, paddr_t paddr)
{
	__asm__ volatile("dc ivac, %0" : : "r"(vaddr));
	dmb();
}
static inline void invalidateByVA_I(vptr_t vaddr, paddr_t paddr)
{
	__asm__ volatile("ic ivau, %0" : : "r"(vaddr));
	dsb();
	isb();
}
static inline void invalidate_I_PoU(void)
{
	__asm__ volatile("ic iallu");
	isb();
}
static inline void cleanInvalByVA(vptr_t vaddr, paddr_t paddr)
{
	__asm__ volatile("dc civac, %0" : : "r"(vaddr));
	dsb();
}
static inline void branchFlush(vptr_t vaddr, paddr_t paddr) {}
static inline word_t getESR(void)
{
	word_t ESR;
	__asm__ volatile("mrs %x0,"
			 "esr_el1"
			 : "=r"(ESR));
	return ESR;
}
static inline word_t getFAR(void)
{
	word_t FAR;
	__asm__ volatile("mrs %x0,"
			 "far_el1"
			 : "=r"(FAR));
	return FAR;
}
static inline word_t ats1e2r(word_t va)
{
	word_t par;
	__asm__ volatile("at s1e2r, %0" ::"r"(va));
	__asm__ volatile("mrs %x0,"
			 "par_el1"
			 : "=r"(par));
	return par;
}
static inline word_t ats1e1r(word_t va)
{
	word_t par;
	__asm__ volatile("at s1e1r, %0" ::"r"(va));
	__asm__ volatile("mrs %x0,"
			 "par_el1"
			 : "=r"(par));
	return par;
}
static inline word_t ats2e0r(word_t va)
{
	word_t par;
	__asm__ volatile("at s12e0r, %0" ::"r"(va));
	__asm__ volatile("mrs %x0,"
			 "par_el1"
			 : "=r"(par));
	return par;
}
void arch_clean_invalidate_caches(void);
void arch_clean_invalidate_L1_caches(word_t type);
/* ARM generic timer implementation */
/* convert to khz first to avoid overflow */
/* but multiply by timer tick ms */
void initTimer(void);
static inline void resetTimer(void)
{
	do {
		word_t _v = ((62500000llu / 1000llu) * 2);
		__asm__ volatile("msr "
				 "cntv_tval_el0"
				 ",%x0" ::"r"(_v));
	} while (0);
	do {
		word_t _v = (1ul << (0));
		__asm__ volatile("msr "
				 "cntv_ctl_el0"
				 ",%x0" ::"r"(_v));
	} while (0);
}
void initGenericTimer(void);
/* #undef CONFIGURE_SMMU */
/* #undef CONFIGURE_SMMU */
/* Each architecture defines a set of constants in #defines. These
 * constants describe the memory regions of the kernel's portion of the
 * address space including the physical memory window, the kernel ELF
 * region, and the device region.
 *
 *  - USER_TOP: The first address after the end of user memory
 *
 *  - PADDR_BASE: The first physical address mapped in the kernel's
 *    physical memory window.
 *  - PPTR_BASE: The first virtual address of the kernel's physical
 *    memory window.
 *  - PPTR_TOP: The first virtual address after the end of the kernel's
 *    physical memory window.
 *
 *  - KERNEL_ELF_PADDR_BASE: The first physical address used to map the
 *    initial kernel image. The kernel ELF is mapped contiguously
 *    starting at this address.
 *  - KERNEL_ELF_BASE: The first virtual address used to map the initial
 *    kernel image.
 *
 *  - KDEV_BASE: The first virtual address used to map devices.
 */
/* The offset from a physical address to a virtual address in the
 * physical memory window. */
/* The last address in the physical memory region mapped into the
 * physical memory window */
/* The kernel base offset is a way to translate the kernel image segment
 * from virtual to physical. This translation must be a single offset
 * for for the entire segment (i.e. the kernel image must be contiguous
 * both virtually and physically) */
/* This symbol is generated by the linker and marks the last valid
 * address in the kernel's virtual region */
extern char ki_end[1];
/* This symbol is generated by the linker and marks the end of boot
 * code/data in kernel image */
extern char ki_boot_end[1];
/* When translating a physical address into an address accessible to the
 * kernel via virtual addressing we always use the mapping of the memory
 * into the physical memory window, even if the mapping originally
 * referred to a kernel virtual address. */
static inline void *ptrFromPAddr(paddr_t paddr)
{
	return (void *)(paddr + (PPTR_BASE - 0x0ul));
}
/* When obtaining a physical address from a reference to any object in
 * the physical mapping window, this function must be used. */
static inline paddr_t addrFromPPtr(const void *pptr)
{
	return (paddr_t)pptr - (PPTR_BASE - 0x0ul);
}
/* When obtaining a physical address from a reference to an address from
 * the kernel ELF mapping, this function must be used. */
static inline paddr_t addrFromKPPtr(const void *pptr)
{
	return (paddr_t)pptr - KERNEL_ELF_BASE_OFFSET;
}
static inline region_t paddr_to_pptr_reg(const p_region_t p_reg)
{
	return (region_t){p_reg.start + (PPTR_BASE - 0x0ul), p_reg.end + (PPTR_BASE - 0x0ul)};
}
static inline p_region_t pptr_to_paddr_reg(const region_t reg)
{
	return (p_region_t){reg.start - (PPTR_BASE - 0x0ul), reg.end - (PPTR_BASE - 0x0ul)};
}
/* ==================== BOOT CODE FINISHES HERE ==================== */
bool_t isVTableRoot(cap_t cap);
bool_t isValidNativeRoot(cap_t cap);
pgde_t *pageUpperDirectoryMapped(asid_t asid, vptr_t vaddr, pude_t *pud);
pude_t *pageDirectoryMapped(asid_t asid, vptr_t vaddr, pde_t *pd);
void unmapPageUpperDirectory(asid_t asid, vptr_t vaddr, pude_t *pud);
void unmapPageDirectory(asid_t asid, vptr_t vaddr, pde_t *pd);
void unmapPageTable(asid_t asid, vptr_t vaddr, pte_t *pt);
void unmapPage(vm_page_size_t page_size, asid_t asid, vptr_t vptr, pptr_t pptr);
void deleteASIDPool(asid_t base, asid_pool_t *pool);
void deleteASID(asid_t asid, vspace_root_t *vspace);
asid_map_t findMapForASID(asid_t asid);
static const region_t *mode_reserved_region = NULL;
static inline exception_t performASIDPoolInvocation(asid_t asid, asid_pool_t *poolPtr, cte_t *cte)
{
	cap_page_global_directory_cap_ptr_set_capPGDMappedASID(&cte->cap, asid);
	cap_page_global_directory_cap_ptr_set_capPGDIsMapped(&cte->cap, 1);
	asid_map_t asid_map = asid_map_asid_map_vspace_new(
		/* vspace_root: reference to vspace root page table object */
		cap_page_global_directory_cap_get_capPGDBasePtr(cte->cap));
	poolPtr->array[asid & ((1ul << (asidLowBits)) - 1ul)] = asid_map;
	return EXCEPTION_NONE;
}
void increaseASIDBindCB(asid_t asid);
void decreaseASIDBindCB(asid_t asid);
cap_t create_it_address_space(cap_t root_cnode_cap, v_region_t it_v_reg);
cap_t create_unmapped_it_frame_cap(pptr_t pptr, bool_t use_large);
cap_t create_mapped_it_frame_cap(cap_t pd_cap, pptr_t pptr, vptr_t vptr, asid_t asid,
				 bool_t use_large, bool_t executable);
void map_kernel_window(void);
void map_kernel_frame(paddr_t paddr, pptr_t vaddr, vm_rights_t vm_rights,
		      vm_attributes_t vm_attributes);
void activate_kernel_vspace(void);
void write_it_asid_pool(cap_t it_ap_cap, cap_t it_pd_cap);
/* ==================== BOOT CODE FINISHES HERE ==================== */
/* need a fake array to get the pointer from the linker script */
extern char arm_vector_table[1];
word_t *lookupIPCBuffer(bool_t isReceiver, tcb_t *thread);
exception_t handleVMFault(tcb_t *thread, vm_fault_type_t vm_faultType);
pde_t *pageTableMapped(asid_t asid, vptr_t vaddr, pte_t *pt);
void setVMRoot(tcb_t *tcb);
bool_t isValidVTableRoot(cap_t cap);
exception_t checkValidIPCBuffer(vptr_t vptr, cap_t cap);
vm_rights_t maskVMRights(vm_rights_t vm_rights, seL4_CapRights_t cap_rights_mask);
exception_t decodeARMMMUInvocation(word_t invLabel, word_t length, cptr_t cptr, cte_t *cte,
				   cap_t cap, word_t *buffer);
void Arch_userStackTrace(tcb_t *tptr);
/* This header was generated by kernel/tools/syscall_header_gen.py.
 *
 * To add a system call number, edit kernel/libsel4/include/api/syscall.xml
 *
 */
enum syscall {
	SysCall = -1,
	SysReplyRecv = -2,
	SysSend = -3,
	SysNBSend = -4,
	SysRecv = -5,
	SysReply = -6,
	SysYield = -7,
	SysNBRecv = -8,
	SysDebugPutChar = -9,
	SysDebugDumpScheduler = -10,
	SysDebugHalt = -11,
	SysDebugCapIdentify = -12,
	SysDebugSnapshot = -13,
	SysDebugNameThread = -14,
};
typedef word_t syscall_t;
/* System call names */
static char *syscall_names[] = {
	[1] = "Call", [2] = "ReplyRecv", [3] = "Send",	[4] = "NBSend",
	[5] = "Recv", [6] = "Reply",	 [7] = "Yield", [8] = "NBRecv",
};
/* the following code can be used at any point in the kernel
 * to determine detail about the kernel entry point */
typedef enum {
	Entry_Interrupt,
	Entry_UnknownSyscall,
	Entry_UserLevelFault,
	Entry_DebugFault,
	Entry_VMFault,
	Entry_Syscall,
	Entry_UnimplementedDevice,
	Entry_VCPUFault,
} entry_type_t;
/**
 * @brief Kernel entry logging
 *
 * Encapsulates useful info about the cause of the kernel entry
 */
typedef struct __attribute__((packed)) kernel_entry {
	seL4_Word path : 3;
	union {
		struct {
			seL4_Word core : 3;
			seL4_Word word : 26;
		};
		/* Tracked kernel entry info filled from outside this file */
		struct {
			seL4_Word syscall_no : 4;
			seL4_Word cap_type : 5;
			seL4_Word is_fastpath : 1;
			seL4_Word invocation_tag : 19;
		};
	};
} kernel_entry_t;
struct lookupCap_ret {
	exception_t status;
	cap_t cap;
};
typedef struct lookupCap_ret lookupCap_ret_t;
struct lookupCapAndSlot_ret {
	exception_t status;
	cap_t cap;
	cte_t *slot;
};
typedef struct lookupCapAndSlot_ret lookupCapAndSlot_ret_t;
struct lookupSlot_raw_ret {
	exception_t status;
	cte_t *slot;
};
typedef struct lookupSlot_raw_ret lookupSlot_raw_ret_t;
struct lookupSlot_ret {
	exception_t status;
	cte_t *slot;
};
typedef struct lookupSlot_ret lookupSlot_ret_t;
struct resolveAddressBits_ret {
	exception_t status;
	cte_t *slot;
	word_t bitsRemaining;
};
typedef struct resolveAddressBits_ret resolveAddressBits_ret_t;
lookupCap_ret_t lookupCap(tcb_t *thread, cptr_t cPtr);
lookupCapAndSlot_ret_t lookupCapAndSlot(tcb_t *thread, cptr_t cPtr);
lookupSlot_raw_ret_t lookupSlot(tcb_t *thread, cptr_t capptr);
lookupSlot_ret_t lookupSlotForCNodeOp(bool_t isSource, cap_t root, cptr_t capptr, word_t depth);
lookupSlot_ret_t lookupSourceSlot(cap_t root, cptr_t capptr, word_t depth);
lookupSlot_ret_t lookupTargetSlot(cap_t root, cptr_t capptr, word_t depth);
lookupSlot_ret_t lookupPivotSlot(cap_t root, cptr_t capptr, word_t depth);
resolveAddressBits_ret_t resolveAddressBits(cap_t nodeCap, cptr_t capptr, word_t n_bits);
extern kernel_entry_t ksKernelEntry;
static inline void benchmark_debug_syscall_start(word_t cptr, word_t msgInfo, word_t syscall)
{
	seL4_MessageInfo_t info = messageInfoFromWord_raw(msgInfo);
	lookupCapAndSlot_ret_t lu_ret = lookupCapAndSlot(ksCurThread, cptr);
	ksKernelEntry.path = Entry_Syscall;
	ksKernelEntry.syscall_no = -syscall;
	ksKernelEntry.cap_type = cap_get_capType(lu_ret.cap);
	ksKernelEntry.invocation_tag = seL4_MessageInfo_get_label(info);
}
void map_kernel_devices(void);
void initL2Cache(void);
void initIRQController(void);
void cpu_initLocalIRQController(void);
void setIRQTrigger(irq_t irq, bool_t trigger);
static inline void plat_cleanL2Range(paddr_t start, paddr_t end);
static inline void plat_invalidateL2Range(paddr_t start, paddr_t end);
static inline void plat_cleanInvalidateL2Range(paddr_t start, paddr_t end);
static inline void plat_cleanInvalidateL2Cache(void);
void cleanInvalidateCacheRange_RAM(word_t start, word_t end, paddr_t pstart);
void cleanCacheRange_RAM(word_t start, word_t end, paddr_t pstart);
void cleanCacheRange_PoU(word_t start, word_t end, paddr_t pstart);
void invalidateCacheRange_RAM(word_t start, word_t end, paddr_t pstart);
void invalidateCacheRange_I(word_t start, word_t end, paddr_t pstart);
void branchFlushRange(word_t start, word_t end, paddr_t pstart);
void clean_D_PoU(void);
void cleanInvalidate_D_PoC(void);
void cleanInvalidate_L1D(void);
void cleanCaches_PoU(void);
void cleanInvalidateL1Caches(void);
/* Cleaning memory before user-level access */
static inline void clearMemory(word_t *ptr, word_t bits)
{
	memzero(ptr, (1ul << (bits)));
	cleanCacheRange_RAM((word_t)ptr, (word_t)ptr + (1ul << (bits)) - 1, addrFromPPtr(ptr));
}
/* Cleaning memory before page table walker access */
static inline void clearMemory_PT(word_t *ptr, word_t bits)
{
	memzero(ptr, (1ul << (bits)));
	cleanCacheRange_PoU((word_t)ptr, (word_t)ptr + (1ul << (bits)) - 1, addrFromPPtr(ptr));
}
/* Update the value of the actual regsiter to hold the expected value */
static inline exception_t Arch_setTLSRegister(word_t tls_base)
{
	/* This register is saved and restored on kernel exit and entry so
	 * we only update it in the saved context. */
	setRegister(ksCurThread, TLS_BASE, tls_base);
	return EXCEPTION_NONE;
}
static inline word_t ready_queues_index(word_t dom, word_t prio)
{
	if (numDomains > 1) {
		return dom * 256 + prio;
	} else {
		return prio;
	}
}
static inline word_t prio_to_l1index(word_t prio)
{
	return (prio >> 6);
}
static inline word_t l1index_to_prio(word_t l1index)
{
	return (l1index << 6);
}
static inline bool_t isRunnable(const tcb_t *thread)
{
	switch (thread_state_get_tsType(thread->tcbState)) {
	case ThreadState_Running:
	case ThreadState_Restart:
		return true;
	default:
		return false;
	}
}
static inline word_t invert_l1index(word_t l1index)
{
	word_t inverted = (((256 + (1 << 6) - 1) / (1 << 6)) - 1 - l1index);
	return inverted;
}
static inline prio_t getHighestPrio(word_t dom)
{
	word_t l1index;
	word_t l2index;
	word_t l1index_inverted;
	/* it's undefined to call clzl on 0 */
	l1index = (1 << 6) - 1 - clzl(ksReadyQueuesL1Bitmap[dom]);
	l1index_inverted = invert_l1index(l1index);
	l2index = (1 << 6) - 1 - clzl(ksReadyQueuesL2Bitmap[dom][l1index_inverted]);
	return (l1index_to_prio(l1index) | l2index);
}
static inline bool_t isHighestPrio(word_t dom, prio_t prio)
{
	return ksReadyQueuesL1Bitmap[dom] == 0 || prio >= getHighestPrio(dom);
}
static inline bool_t isBlocked(const tcb_t *thread)
{
	switch (thread_state_get_tsType(thread->tcbState)) {
	case ThreadState_BlockedOnReceive:
	case ThreadState_BlockedOnSend:
	case ThreadState_BlockedOnNotification:
	case ThreadState_BlockedOnReply:
		return true;
	default:
		return false;
	}
}
static inline bool_t isStopped(const tcb_t *thread)
{
	switch (thread_state_get_tsType(thread->tcbState)) {
	case ThreadState_Inactive:
	case ThreadState_BlockedOnReceive:
	case ThreadState_BlockedOnSend:
	case ThreadState_BlockedOnNotification:
	case ThreadState_BlockedOnReply:
		return true;
	default:
		return false;
	}
}
void Arch_switchToThread(tcb_t *tcb);
void Arch_switchToIdleThread(void);
void Arch_configureIdleThread(tcb_t *tcb);
void Arch_activateIdleThread(tcb_t *tcb);
void idle_thread(void);
void configureIdleThread(tcb_t *tcb);
void activateThread(void);
void suspend(tcb_t *target);
void restart(tcb_t *target);
void doIPCTransfer(tcb_t *sender, endpoint_t *endpoint, word_t badge, bool_t grant,
		   tcb_t *receiver);
void doReplyTransfer(tcb_t *sender, tcb_t *receiver, cte_t *slot, bool_t grant);
void timerTick(void);
void doNormalTransfer(tcb_t *sender, word_t *sendBuffer, endpoint_t *endpoint, word_t badge,
		      bool_t canGrant, tcb_t *receiver, word_t *receiveBuffer);
void doFaultTransfer(word_t badge, tcb_t *sender, tcb_t *receiver, word_t *receiverIPCBuffer);
void doNBRecvFailedTransfer(tcb_t *thread);
void schedule(void);
void chooseThread(void);
void switchToThread(tcb_t *thread);
void switchToIdleThread(void);
void setDomain(tcb_t *tptr, dom_t dom);
void setPriority(tcb_t *tptr, prio_t prio);
void setMCPriority(tcb_t *tptr, prio_t mcp);
void scheduleTCB(tcb_t *tptr);
void possibleSwitchTo(tcb_t *tptr);
void setThreadState(tcb_t *tptr, _thread_state_t ts);
void rescheduleRequired(void);
/* declare that the thread has had its registers (in its user_context_t) modified and it
 * should ignore any 'efficient' restores next time it is run, and instead restore all
 * registers into their correct place */
void Arch_postModifyRegisters(tcb_t *tptr);
/* Updates a threads FaultIP to match its NextIP. This is used to indicate that a
 * thread has completed its fault and by updating the restartPC means that if the thread
 * should get restarted in the future for any reason it is restart in such a way as to
 * not cause the fault again. */
static inline void updateRestartPC(tcb_t *tcb)
{
	setRegister(tcb, FaultIP, getRegister(tcb, NextIP));
}
static inline void debug_printKernelEntryReason(void)
{
	printf("\nKernel entry via ");
	switch (ksKernelEntry.path) {
	case Entry_Interrupt:
		printf("Interrupt, irq %lu\n", (unsigned long)ksKernelEntry.word);
		break;
	case Entry_UnknownSyscall:
		printf("Unknown syscall, word: %lu", (unsigned long)ksKernelEntry.word);
		break;
	case Entry_VMFault:
		printf("VM Fault, fault type: %lu\n", (unsigned long)ksKernelEntry.word);
		break;
	case Entry_UserLevelFault:
		printf("User level fault, number: %lu", (unsigned long)ksKernelEntry.word);
		break;
	case Entry_Syscall:
		printf("Syscall, number: %ld, %s\n", (long)ksKernelEntry.syscall_no,
		       syscall_names[ksKernelEntry.syscall_no]);
		if (ksKernelEntry.syscall_no == -SysSend ||
		    ksKernelEntry.syscall_no == -SysNBSend ||
		    ksKernelEntry.syscall_no == -SysCall) {
			printf("Cap type: %lu, Invocation tag: %lu\n",
			       (unsigned long)ksKernelEntry.cap_type,
			       (unsigned long)ksKernelEntry.invocation_tag);
		}
		break;
	case Entry_VCPUFault:
		printf("VCPUFault\n");
		break;
	default:
		printf("Unknown (%u)\n", ksKernelEntry.path);
		break;
	}
}
/* Prints the user context and stack trace of the current thread */
static inline void debug_printUserState(void)
{
	tcb_t *tptr = ksCurThread;
	printf("Current thread: %s\n",
	       ((debug_tcb_t *)(((cte_t *)((word_t)(tptr) & ~((1ul << (11)) - 1ul))) +
				(tcbCNodeEntries)))
		       ->tcbName);
	printf("Next instruction adress: %lx\n", getRestartPC(tptr));
	printf("Stack:\n");
	Arch_userStackTrace(tptr);
}
static inline void debug_printTCB(tcb_t *tcb)
{
	printf("%40s\t", ((debug_tcb_t *)(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) +
					  (tcbCNodeEntries)))
				 ->tcbName);
	char *state;
	switch (thread_state_get_tsType(tcb->tcbState)) {
	case ThreadState_Inactive:
		state = "inactive";
		break;
	case ThreadState_Running:
		state = "running";
		break;
	case ThreadState_Restart:
		state = "restart";
		break;
	case ThreadState_BlockedOnReceive:
		state = "blocked on recv";
		break;
	case ThreadState_BlockedOnSend:
		state = "blocked on send";
		break;
	case ThreadState_BlockedOnReply:
		state = "blocked on reply";
		break;
	case ThreadState_BlockedOnNotification:
		state = "blocked on ntfn";
		break;
	case ThreadState_IdleThreadState:
		state = "idle";
		break;
	default:
		_fail("Unknown thread state",
		      "/home/lab/projects/seL4/seL4test/kernel/include/api/debug.h", 113, __func__);
	}
	word_t core = 0;
	printf("%15s\t%p\t%20lu\t%lu", state, (void *)getRestartPC(tcb), tcb->tcbPriority, core);
	printf("\n");
}
static inline void debug_dumpScheduler(void)
{
	printf("Dumping all tcbs!\n");
	printf("Name                                    \tState          \tIP                  \t "
	       "Prio \t Core%s\n",
	       0 ? "\t InReleaseQueue" : "");
	printf("-----------------------------------------------------------------------------------"
	       "---\n");
	for (tcb_t *curr = ksDebugTCBs; curr != NULL;
	     curr = ((debug_tcb_t *)(((cte_t *)((word_t)(curr) & ~((1ul << (11)) - 1ul))) +
				     (tcbCNodeEntries)))
			    ->tcbDebugNext) {
		debug_printTCB(curr);
	}
}
exception_t handleSyscall(syscall_t syscall);
exception_t handleInterruptEntry(void);
exception_t handleUnknownSyscall(word_t w);
exception_t handleUserLevelFault(word_t w_a, word_t w_b);
exception_t handleVMFaultEvent(vm_fault_type_t vm_faultType);
static inline word_t getSyscallArg(word_t i, word_t *ipc_buffer)
{
	if (i < n_msgRegisters) {
		return getRegister(ksCurThread, msgRegisters[i]);
	}
	return ipc_buffer[i + 1];
}
extern extra_caps_t current_extra_caps;
static inline word_t sanitiseRegister(register_t reg, word_t v, bool_t archInfo)
{
	if (reg == SPSR_EL1) {
		if (archInfo) {
			switch (v & 0x1f) {
			case 0:
			case 4:
			case 5:
				return v;
			default:
				break;
			}
		}
		return (v & 0xf0000000) | ((1 << 6) | 0 | 0);
	} else {
		return v;
	}
}
static inline bool_t Arch_getSanitiseRegisterInfo(tcb_t *thread)
{
	return 0;
}
/* consistency with libsel4 */
_Static_assert(lookup_fault_invalid_root + 1 == seL4_InvalidRoot, "InvalidRoot");
_Static_assert(lookup_fault_missing_capability + 1 == seL4_MissingCapability, "MissingCapability");
_Static_assert(lookup_fault_depth_mismatch + 1 == seL4_DepthMismatch, "DepthMismatch");
_Static_assert(lookup_fault_guard_mismatch + 1 == seL4_GuardMismatch, "GuardMismatch");
_Static_assert((word_t)n_syscallMessage == seL4_UnknownSyscall_Syscall,
	       "seL4_UnknownSyscall_Syscall");
_Static_assert((word_t)n_exceptionMessage == seL4_UserException_Number,
	       "seL4_UserException_Number");
_Static_assert((word_t)n_exceptionMessage + 1 == seL4_UserException_Code,
	       "seL4_UserException_Code");
static inline unsigned int setMRs_lookup_failure(tcb_t *receiver, word_t *receiveIPCBuffer,
						 lookup_fault_t luf, unsigned int offset)
{
	word_t lufType = lookup_fault_get_lufType(luf);
	word_t i;
	i = setMR(receiver, receiveIPCBuffer, offset, lufType + 1);
	/* check constants match libsel4 */
	if (offset == seL4_CapFault_LookupFailureType) {
	} else {
	}
	switch (lufType) {
	case lookup_fault_invalid_root:
		return i;
	case lookup_fault_missing_capability:
		return setMR(receiver, receiveIPCBuffer, offset + 1,
			     lookup_fault_missing_capability_get_bitsLeft(luf));
	case lookup_fault_depth_mismatch:
		setMR(receiver, receiveIPCBuffer, offset + 1,
		      lookup_fault_depth_mismatch_get_bitsLeft(luf));
		return setMR(receiver, receiveIPCBuffer, offset + 2,
			     lookup_fault_depth_mismatch_get_bitsFound(luf));
	case lookup_fault_guard_mismatch:
		setMR(receiver, receiveIPCBuffer, offset + 1,
		      lookup_fault_guard_mismatch_get_bitsLeft(luf));
		setMR(receiver, receiveIPCBuffer, offset + 2,
		      lookup_fault_guard_mismatch_get_guardFound(luf));
		return setMR(receiver, receiveIPCBuffer, offset + 3,
			     lookup_fault_guard_mismatch_get_bitsFound(luf));
	default:
		_fail("Invalid lookup failure",
		      "/home/lab/projects/seL4/seL4test/kernel/src/api/faults.c", 70, __func__);
	}
}
static inline void copyMRsFaultReply(tcb_t *sender, tcb_t *receiver, MessageID_t id, word_t length)
{
	word_t i;
	bool_t archInfo;
	archInfo = Arch_getSanitiseRegisterInfo(receiver);
	for (i = 0; i < (((length) < (n_msgRegisters)) ? (length) : (n_msgRegisters)); i++) {
		register_t r = fault_messages[id][i];
		word_t v = getRegister(sender, msgRegisters[i]);
		setRegister(receiver, r, sanitiseRegister(r, v, archInfo));
	}
	if (i < length) {
		word_t *sendBuf = lookupIPCBuffer(false, sender);
		if (sendBuf) {
			for (; i < length; i++) {
				register_t r = fault_messages[id][i];
				word_t v = sendBuf[i + 1];
				setRegister(receiver, r, sanitiseRegister(r, v, archInfo));
			}
		}
	}
}
static inline void copyMRsFault(tcb_t *sender, tcb_t *receiver, MessageID_t id, word_t length,
				word_t *receiveIPCBuffer)
{
	word_t i;
	for (i = 0; i < (((length) < (n_msgRegisters)) ? (length) : (n_msgRegisters)); i++) {
		setRegister(receiver, msgRegisters[i], getRegister(sender, fault_messages[id][i]));
	}
	if (receiveIPCBuffer) {
		for (; i < length; i++) {
			receiveIPCBuffer[i + 1] = getRegister(sender, fault_messages[id][i]);
		}
	}
}
bool_t handleFaultReply(tcb_t *receiver, tcb_t *sender)
{
	/* These lookups are moved inward from doReplyTransfer */
	seL4_MessageInfo_t tag = messageInfoFromWord(getRegister(sender, msgInfoRegister));
	word_t label = seL4_MessageInfo_get_label(tag);
	word_t length = seL4_MessageInfo_get_length(tag);
	seL4_Fault_t fault = receiver->tcbFault;
	switch (seL4_Fault_get_seL4_FaultType(fault)) {
	case seL4_Fault_CapFault:
		return true;
	case seL4_Fault_UnknownSyscall:
		copyMRsFaultReply(
			sender, receiver, MessageID_Syscall,
			(((length) < (n_syscallMessage)) ? (length) : (n_syscallMessage)));
		return (label == 0);
	case seL4_Fault_UserException:
		copyMRsFaultReply(
			sender, receiver, MessageID_Exception,
			(((length) < (n_exceptionMessage)) ? (length) : (n_exceptionMessage)));
		return (label == 0);
	default:
		return Arch_handleFaultReply(receiver, sender,
					     seL4_Fault_get_seL4_FaultType(fault));
	}
}
word_t setMRs_fault(tcb_t *sender, tcb_t *receiver, word_t *receiveIPCBuffer)
{
	switch (seL4_Fault_get_seL4_FaultType(sender->tcbFault)) {
	case seL4_Fault_CapFault:
		setMR(receiver, receiveIPCBuffer, seL4_CapFault_IP, getRestartPC(sender));
		setMR(receiver, receiveIPCBuffer, seL4_CapFault_Addr,
		      seL4_Fault_CapFault_get_address(sender->tcbFault));
		setMR(receiver, receiveIPCBuffer, seL4_CapFault_InRecvPhase,
		      seL4_Fault_CapFault_get_inReceivePhase(sender->tcbFault));
		return setMRs_lookup_failure(receiver, receiveIPCBuffer, sender->tcbLookupFailure,
					     seL4_CapFault_LookupFailureType);
	case seL4_Fault_UnknownSyscall: {
		copyMRsFault(sender, receiver, MessageID_Syscall, n_syscallMessage,
			     receiveIPCBuffer);
		return setMR(receiver, receiveIPCBuffer, n_syscallMessage,
			     seL4_Fault_UnknownSyscall_get_syscallNumber(sender->tcbFault));
	}
	case seL4_Fault_UserException: {
		copyMRsFault(sender, receiver, MessageID_Exception, n_exceptionMessage,
			     receiveIPCBuffer);
		setMR(receiver, receiveIPCBuffer, n_exceptionMessage,
		      seL4_Fault_UserException_get_number(sender->tcbFault));
		return setMR(receiver, receiveIPCBuffer, n_exceptionMessage + 1u,
			     seL4_Fault_UserException_get_code(sender->tcbFault));
	}
	default:
		return Arch_setMRs_fault(sender, receiver, receiveIPCBuffer,
					 seL4_Fault_get_seL4_FaultType(sender->tcbFault));
	}
}
struct deriveCap_ret {
	exception_t status;
	cap_t cap;
};
typedef struct deriveCap_ret deriveCap_ret_t;
struct finaliseCap_ret {
	cap_t remainder;
	/* potential cap holding information for cleanup that needs to be happen *after* a
	 * cap has been deleted. Where deleted here means been removed from the slot in emptySlot */
	cap_t cleanupInfo;
};
typedef struct finaliseCap_ret finaliseCap_ret_t;
deriveCap_ret_t Arch_deriveCap(cte_t *slot, cap_t cap);
cap_t Arch_updateCapData(bool_t preserve, word_t data, cap_t cap);
cap_t Arch_maskCapRights(seL4_CapRights_t cap_rights_mask, cap_t cap);
finaliseCap_ret_t Arch_finaliseCap(cap_t cap, bool_t final);
bool_t Arch_sameRegionAs(cap_t cap_a, cap_t cap_b);
bool_t Arch_sameObjectAs(cap_t cap_a, cap_t cap_b);
bool_t Arch_isFrameType(word_t type);
cap_t Arch_createObject(object_t t, void *regionBase, word_t userSize, bool_t deviceMemory);
exception_t Arch_decodeInvocation(word_t invLabel, word_t length, cptr_t cptr, cte_t *slot,
				  cap_t cap, bool_t call, word_t *buffer);
void Arch_prepareThreadDelete(tcb_t *thread);
word_t Arch_getObjectSize(word_t t);
static inline void Arch_postCapDeletion(cap_t cap) {}
exception_t Arch_decodeIRQControlInvocation(word_t invLabel, word_t length, cte_t *srcSlot,
					    word_t *buffer);
/* Handle a platform-reserved IRQ. */
static inline void handleReservedIRQ(irq_t irq)
{
	printf("Received unhandled reserved IRQ: 0x%lx\n", (irq));
}
static inline exception_t Arch_checkIRQ(word_t irq_w)
{
	if (irq_w > maxIRQ) {
		current_syscall_error.type = seL4_RangeError;
		current_syscall_error.rangeErrorMin = 0;
		current_syscall_error.rangeErrorMax = maxIRQ;
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Rejecting request for IRQ "
			       "%u. IRQ is greater than maxIRQ.>>\n",
			       0lu, __func__, 60, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), (int)irq_w);
		} while (0);
		return EXCEPTION_SYSCALL_ERROR;
	}
	return EXCEPTION_NONE;
}
exception_t decodeIRQControlInvocation(word_t invLabel, word_t length, cte_t *srcSlot,
				       word_t *buffer);
exception_t invokeIRQControl(irq_t irq, cte_t *handlerSlot, cte_t *controlSlot);
exception_t decodeIRQHandlerInvocation(word_t invLabel, irq_t irq);
void invokeIRQHandler_AckIRQ(irq_t irq);
void invokeIRQHandler_SetIRQHandler(irq_t irq, cap_t cap, cte_t *slot);
void invokeIRQHandler_ClearIRQHandler(irq_t irq);
void deletingIRQHandler(irq_t irq);
void deletedIRQHandler(irq_t irq);
void handleInterrupt(irq_t irq);
bool_t isIRQActive(irq_t irq);
void setIRQState(irq_state_t irqState, irq_t irq);
deriveCap_ret_t deriveCap(cte_t *slot, cap_t cap);
finaliseCap_ret_t finaliseCap(cap_t cap, bool_t final, bool_t exposed);
bool_t hasCancelSendRights(cap_t cap);
bool_t sameRegionAs(cap_t cap_a, cap_t cap_b);
bool_t sameObjectAs(cap_t cap_a, cap_t cap_b);
cap_t updateCapData(bool_t preserve, word_t newData, cap_t cap);
cap_t maskCapRights(seL4_CapRights_t seL4_CapRights, cap_t cap);
cap_t createObject(object_t t, void *regionBase, word_t, bool_t deviceMemory);
void createNewObjects(object_t t, cte_t *parent, cte_t *destCNode, word_t destOffset,
		      word_t destLength, void *regionBase, word_t userSize, bool_t deviceMemory);
exception_t decodeInvocation(word_t invLabel, word_t length, cptr_t capIndex, cte_t *slot,
			     cap_t cap, bool_t block, bool_t call, word_t *buffer);
exception_t performInvocation_Endpoint(endpoint_t *ep, word_t badge, bool_t canGrant,
				       bool_t canGrantReply, bool_t block, bool_t call);
exception_t performInvocation_Notification(notification_t *ntfn, word_t badge);
exception_t performInvocation_Reply(tcb_t *thread, cte_t *slot, bool_t canGrant);
word_t getObjectSize(word_t t, word_t userObjSize);
static inline void postCapDeletion(cap_t cap)
{
	if (cap_get_capType(cap) == cap_irq_handler_cap) {
		irq_t irq = (cap_irq_handler_cap_get_capIRQ(cap));
		deletedIRQHandler(irq);
	} else if (isArchCap(cap)) {
		Arch_postCapDeletion(cap);
	}
}
word_t cap_get_capSizeBits(cap_t cap);
bool_t cap_get_capIsPhysical(cap_t cap);
void *cap_get_capPtr(cap_t cap);
bool_t isCapRevocable(cap_t derivedCap, cap_t srcCap);
void sendSignal(notification_t *ntfnPtr, word_t badge);
void receiveSignal(tcb_t *thread, cap_t cap, bool_t isBlocking);
void cancelAllSignals(notification_t *ntfnPtr);
void cancelSignal(tcb_t *threadPtr, notification_t *ntfnPtr);
void completeSignal(notification_t *ntfnPtr, tcb_t *tcb);
void unbindMaybeNotification(notification_t *ntfnPtr);
void unbindNotification(tcb_t *tcb);
void bindNotification(tcb_t *tcb, notification_t *ntfnPtr);
static inline tcb_queue_t ep_ptr_get_queue(endpoint_t *epptr)
{
	tcb_queue_t queue;
	queue.head = (tcb_t *)endpoint_ptr_get_epQueue_head(epptr);
	queue.end = (tcb_t *)endpoint_ptr_get_epQueue_tail(epptr);
	return queue;
}
void sendIPC(bool_t blocking, bool_t do_call, word_t badge, bool_t canGrant, bool_t canGrantReply,
	     tcb_t *thread, endpoint_t *epptr);
void receiveIPC(tcb_t *thread, cap_t cap, bool_t isBlocking);
void cancelIPC(tcb_t *tptr);
void cancelAllIPC(endpoint_t *epptr);
void cancelBadgedSends(endpoint_t *epptr, word_t badge);
void replyFromKernel_error(tcb_t *thread);
void replyFromKernel_success_empty(tcb_t *thread);
/* It is assumed that every untyped is within seL4_MinUntypedBits and seL4_MaxUntypedBits
 * (inclusive). This means that every untyped stored as seL4_MinUntypedBits
 * subtracted from its size before it is stored in capBlockSize, and
 * capFreeIndex counts in chunks of size 2^seL4_MinUntypedBits. The seL4_MaxUntypedBits
 * is the minimal untyped that can be stored when considering both how
 * many bits of capBlockSize there are, and the largest offset that can
 * be stored in capFreeIndex */
exception_t decodeUntypedInvocation(word_t invLabel, word_t length, cte_t *slot, cap_t cap,
				    bool_t call, word_t *buffer);
exception_t invokeUntyped_Retype(cte_t *srcSlot, bool_t reset, void *retypeBase, object_t newType,
				 word_t userSize, cte_t *destCNode, word_t destOffset,
				 word_t destLength, bool_t deviceMemory);
exception_t sendFaultIPC(tcb_t *tptr);
void handleDoubleFault(tcb_t *tptr, seL4_Fault_t ex1);
void handleFault(tcb_t *tptr);
word_t strnlen(const char *s, word_t maxlen);
word_t strlcpy(char *dest, const char *src, word_t size);
word_t strlcat(char *dest, const char *src, word_t size);
static inline void arch_c_entry_hook(void)
{
	arm_save_thread_id(ksCurThread);
}
static inline void arch_c_exit_hook(void)
{
	arm_load_thread_id(ksCurThread);
}
void restore_user_context(void);
void c_handle_syscall(word_t cptr, word_t msgInfo, syscall_t syscall)
	__attribute__((__section__(".vectors.text")));
void c_handle_fastpath_call(word_t cptr, word_t msgInfo)
	__attribute__((__section__(".vectors.text")));
void c_handle_fastpath_reply_recv(word_t cptr, word_t msgInfo)
	__attribute__((__section__(".vectors.text")));
void c_handle_interrupt(void) __attribute__((__section__(".vectors.text")));
void c_handle_undefined_instruction(void) __attribute__((__section__(".vectors.text")));
void c_handle_data_fault(void) __attribute__((__section__(".vectors.text")));
void c_handle_instruction_fault(void) __attribute__((__section__(".vectors.text")));
void c_handle_enfp(void) __attribute__((__section__(".vectors.text")));
/* This C function should be the first thing called from C after entry from
 * assembly. It provides a single place to do any entry work that is not
 * done in assembly for various reasons */
static inline void c_entry_hook(void)
{
	arch_c_entry_hook();
}
/* This C function should be the last thing called from C before exiting
 * the kernel (be it to assembly or returning to user space). It provides
 * a place to provide any additional instrumentation or functionality
 * in C before leaving the kernel */
static inline void c_exit_hook(void)
{
	arch_c_exit_hook();
}
/* helpers */
void add_to_seen(cap_t c);
void reset_seen_list(void);
bool_t seen(cap_t c);
bool_t same_cap(cap_t a, cap_t b);
bool_t root_or_idle_tcb(tcb_t *tcb);
word_t get_tcb_sp(tcb_t *tcb);
/* common */
void debug_capDL(void);
void obj_tcb_print_cnodes(cap_t cnode, tcb_t *tcb);
void print_caps(void);
void print_objects(void);
void print_cap(cap_t cap);
void print_object(cap_t cap);
void obj_tcb_print_attrs(tcb_t *tcb);
void obj_sc_print_attrs(cap_t sc);
void obj_cnode_print_attrs(cap_t cnode);
void obj_ut_print_attrs(cte_t *slot, tcb_t *tcb);
void obj_tcb_print_slots(tcb_t *tcb);
void obj_cnode_print_slots(tcb_t *tcb);
void obj_irq_print_slots(cap_t irq_cap);
void obj_irq_print_maps(void);
void cap_ep_print_attrs(cap_t ep);
void cap_ntfn_print_attrs(cap_t ntfn);
void cap_cnode_print_attrs(cap_t cnode);
/* arch specific functions */
void print_ipc_buffer_slot(tcb_t *tcb);
/* TBD: currently the capDL extractor declaring an object for every entry in the vspace.
 * However, frames can be mapped into multiple locations but sould only be declared once.
 */
void obj_vtable_print_slots(tcb_t *tcb);
void print_cap_arch(cap_t cap);
void print_object_arch(cap_t cap);
void obj_tcb_print_vtable(tcb_t *tcb);
static inline void obj_asidpool_print_attrs(cap_t asid_cap)
{
	printf("(asid_high: 0x%lx)\n",
	       (long unsigned int)((cap_asid_pool_cap_get_capASIDBase(asid_cap) >> asidLowBits) &
				   ((1ul << (asidHighBits)) - 1ul)));
}
/* The haskell function 'handleEvent' is split into 'handleXXX' variants
 * for each event causing a kernel entry */
exception_t handleInterruptEntry(void)
{
	irq_t irq;
	irq = getActiveIRQ();
	if ((irq) != (irqInvalid)) {
		handleInterrupt(irq);
	} else {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Spurious interrupt!>>\n",
			       0lu, __func__, 53, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		handleSpuriousIRQ();
	}
	schedule();
	activateThread();
	return EXCEPTION_NONE;
}
exception_t handleUnknownSyscall(word_t w)
{
	if (w == SysDebugPutChar) {
		kernel_putchar(getRegister(ksCurThread, capRegister));
		return EXCEPTION_NONE;
	}
	if (w == SysDebugDumpScheduler) {
		debug_dumpScheduler();
		return EXCEPTION_NONE;
	}
	if (w == SysDebugHalt) {
		tcb_t *tptr = ksCurThread;
		printf("Debug halt syscall from user thread %p \"%s\"\n", tptr,
		       ((debug_tcb_t *)(((cte_t *)((word_t)(tptr) & ~((1ul << (11)) - 1ul))) +
					(tcbCNodeEntries)))
			       ->tcbName);
		halt();
	}
	if (w == SysDebugSnapshot) {
		tcb_t *tptr = ksCurThread;
		printf("Debug snapshot syscall from user thread %p \"%s\"\n", tptr,
		       ((debug_tcb_t *)(((cte_t *)((word_t)(tptr) & ~((1ul << (11)) - 1ul))) +
					(tcbCNodeEntries)))
			       ->tcbName);
		debug_capDL();
		return EXCEPTION_NONE;
	}
	if (w == SysDebugCapIdentify) {
		word_t cptr = getRegister(ksCurThread, capRegister);
		lookupCapAndSlot_ret_t lu_ret = lookupCapAndSlot(ksCurThread, cptr);
		word_t cap_type = cap_get_capType(lu_ret.cap);
		setRegister(ksCurThread, capRegister, cap_type);
		return EXCEPTION_NONE;
	}
	if (w == SysDebugNameThread) {
		/* This is a syscall meant to aid debugging, so if anything goes wrong
		 * then assume the system is completely misconfigured and halt */
		const char *name;
		word_t len;
		word_t cptr = getRegister(ksCurThread, capRegister);
		lookupCapAndSlot_ret_t lu_ret = lookupCapAndSlot(ksCurThread, cptr);
		/* ensure we got a TCB cap */
		word_t cap_type = cap_get_capType(lu_ret.cap);
		if (cap_type != cap_thread_cap) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: "
				       "SysDebugNameThread: cap is not a TCB, halting>>\n",
				       0lu, __func__, 115, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			halt();
		}
		/* Add 1 to the IPC buffer to skip the message info word */
		name = (const char *)(lookupIPCBuffer(true, ksCurThread) + 1);
		if (!name) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: "
				       "SysDebugNameThread: Failed to lookup IPC buffer, "
				       "halting>>\n",
				       0lu, __func__, 121, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			halt();
		}
		/* ensure the name isn't too long */
		len = strnlen(name, seL4_MsgMaxLength * sizeof(word_t));
		if (len == seL4_MsgMaxLength * sizeof(word_t)) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: "
				       "SysDebugNameThread: Name too long, halting>>\n",
				       0lu, __func__, 127, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			halt();
		}
		setThreadName(((tcb_t *)(cap_thread_cap_get_capTCBPtr(lu_ret.cap))), name);
		return EXCEPTION_NONE;
	}
	{
		{
			current_fault = seL4_Fault_UnknownSyscall_new(w);
			handleFault(ksCurThread);
		}
	}
	schedule();
	activateThread();
	return EXCEPTION_NONE;
}
exception_t handleUserLevelFault(word_t w_a, word_t w_b)
{
	{
		{
			current_fault = seL4_Fault_UserException_new(w_a, w_b);
			handleFault(ksCurThread);
		}
	}
	schedule();
	activateThread();
	return EXCEPTION_NONE;
}
exception_t handleVMFaultEvent(vm_fault_type_t vm_faultType)
{
	exception_t status = handleVMFault(ksCurThread, vm_faultType);
	if (status != EXCEPTION_NONE) {
		handleFault(ksCurThread);
	}

	schedule();
	activateThread();
	return EXCEPTION_NONE;
}
static exception_t handleInvocation(bool_t isCall, bool_t isBlocking)
{
	seL4_MessageInfo_t info;
	lookupCapAndSlot_ret_t lu_ret;
	word_t *buffer;
	exception_t status;
	word_t length;
	tcb_t *thread;
	thread = ksCurThread;
	info = messageInfoFromWord(getRegister(thread, msgInfoRegister));
	cptr_t cptr = getRegister(thread, capRegister);
	/* faulting section */
	lu_ret = lookupCapAndSlot(thread, cptr);
	if (__builtin_expect(!!(lu_ret.status != EXCEPTION_NONE), 0)) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Invocation of invalid cap "
			       "#%lu.>>\n",
			       0lu, __func__, 283, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), cptr);
		} while (0);
		current_fault = seL4_Fault_CapFault_new(cptr, false);
		if (isBlocking) {
			handleFault(thread);
		}
		return EXCEPTION_NONE;
	}
	buffer = lookupIPCBuffer(false, thread);
	status = lookupExtraCaps(thread, buffer, info);
	if (__builtin_expect(!!(status != EXCEPTION_NONE), 0)) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Lookup of extra caps "
			       "failed.>>\n",
			       0lu, __func__, 298, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		if (isBlocking) {
			handleFault(thread);
		}
		return EXCEPTION_NONE;
	}
	/* Syscall error/Preemptible section */
	length = seL4_MessageInfo_get_length(info);
	if (__builtin_expect(!!(length > n_msgRegisters && !buffer), 0)) {
		length = n_msgRegisters;
	}
	status = decodeInvocation(seL4_MessageInfo_get_label(info), length, cptr, lu_ret.slot,
				  lu_ret.cap, isBlocking, isCall, buffer);
	if (__builtin_expect(!!(status == EXCEPTION_PREEMPTED), 0)) {
		return status;
	}
	if (__builtin_expect(!!(status == EXCEPTION_SYSCALL_ERROR), 0)) {
		if (isCall) {
			replyFromKernel_error(thread);
		}
		return EXCEPTION_NONE;
	}
	if (__builtin_expect(!!(thread_state_get_tsType(thread->tcbState) == ThreadState_Restart),
			     0)) {
		if (isCall) {
			replyFromKernel_success_empty(thread);
		}
		setThreadState(thread, ThreadState_Running);
	}
	return EXCEPTION_NONE;
}
static void handleReply(void)
{
	cte_t *callerSlot;
	cap_t callerCap;
	callerSlot = (((cte_t *)((word_t)(ksCurThread) & ~((1ul << (11)) - 1ul))) + (tcbCaller));
	callerCap = callerSlot->cap;
	switch (cap_get_capType(callerCap)) {
	case cap_reply_cap: {
		tcb_t *caller;
		if (cap_reply_cap_get_capReplyMaster(callerCap)) {
			break;
		}
		caller = ((tcb_t *)(cap_reply_cap_get_capTCBPtr(callerCap)));
		/* Haskell error:
		 * "handleReply: caller must not be the current thread" */
		doReplyTransfer(ksCurThread, caller, callerSlot,
				cap_reply_cap_get_capReplyCanGrant(callerCap));
		return;
	}
	case cap_null_cap:
		/* Do nothing when no caller is pending */
		return;
	default:
		break;
	}
	_fail("handleReply: invalid caller cap",
	      "/home/lab/projects/seL4/seL4test/kernel/src/api/syscall.c", 398, __func__);
}
static void handleRecv(bool_t isBlocking)
{
	word_t epCPtr;
	lookupCap_ret_t lu_ret;
	epCPtr = getRegister(ksCurThread, capRegister);
	lu_ret = lookupCap(ksCurThread, epCPtr);
	if (__builtin_expect(!!(lu_ret.status != EXCEPTION_NONE), 0)) {
		/* current_lookup_fault has been set by lookupCap */
		current_fault = seL4_Fault_CapFault_new(epCPtr, true);
		handleFault(ksCurThread);
		return;
	}
	switch (cap_get_capType(lu_ret.cap)) {
	case cap_endpoint_cap:
		if (__builtin_expect(!!(!cap_endpoint_cap_get_capCanReceive(lu_ret.cap)), 0)) {
			current_lookup_fault = lookup_fault_missing_capability_new(0);
			current_fault = seL4_Fault_CapFault_new(epCPtr, true);
			handleFault(ksCurThread);
			break;
		}
		deleteCallerCap(ksCurThread);
		receiveIPC(ksCurThread, lu_ret.cap, isBlocking);
		break;
	case cap_notification_cap: {
		notification_t *ntfnPtr;
		tcb_t *boundTCB;
		ntfnPtr = ((notification_t *)(cap_notification_cap_get_capNtfnPtr(lu_ret.cap)));
		boundTCB = (tcb_t *)notification_ptr_get_ntfnBoundTCB(ntfnPtr);
		if (__builtin_expect(!!(!cap_notification_cap_get_capNtfnCanReceive(lu_ret.cap) ||
					(boundTCB && boundTCB != ksCurThread)),
				     0)) {
			current_lookup_fault = lookup_fault_missing_capability_new(0);
			current_fault = seL4_Fault_CapFault_new(epCPtr, true);
			handleFault(ksCurThread);
			break;
		}
		receiveSignal(ksCurThread, lu_ret.cap, isBlocking);
		break;
	}
	default:
		current_lookup_fault = lookup_fault_missing_capability_new(0);
		current_fault = seL4_Fault_CapFault_new(epCPtr, true);
		handleFault(ksCurThread);
		break;
	}
}
static void handleYield(void)
{
	tcbSchedDequeue(ksCurThread);
	tcbSchedAppend(ksCurThread);
	rescheduleRequired();
}
exception_t handleSyscall(syscall_t syscall)
{
	exception_t ret;
	irq_t irq;
	{
		{
			switch (syscall) {
			case SysSend:
				ret = handleInvocation(false, true);
				if (__builtin_expect(!!(ret != EXCEPTION_NONE), 0)) {
					irq = getActiveIRQ();
					if ((irq) != (irqInvalid)) {
						handleInterrupt(irq);
					}
				}
				break;
			case SysNBSend:
				ret = handleInvocation(false, false);
				if (__builtin_expect(!!(ret != EXCEPTION_NONE), 0)) {
					irq = getActiveIRQ();
					if ((irq) != (irqInvalid)) {
						handleInterrupt(irq);
					}
				}
				break;
			case SysCall:
				ret = handleInvocation(true, true);
				if (__builtin_expect(!!(ret != EXCEPTION_NONE), 0)) {
					irq = getActiveIRQ();
					if ((irq) != (irqInvalid)) {
						handleInterrupt(irq);
					}
				}
				break;
			case SysRecv:
				handleRecv(true);
				break;
			case SysReply:
				handleReply();
				break;
			case SysReplyRecv:
				handleReply();
				handleRecv(true);
				break;
			case SysNBRecv:
				handleRecv(false);
				break;
			case SysYield:
				handleYield();
				break;
			default:
				_fail("Invalid syscall",
				      "/home/lab/projects/seL4/seL4test/kernel/src/api/syscall.c",
				      622, __func__);
			}
		}
	}
	schedule();
	activateThread();
	return EXCEPTION_NONE;
}
static inline void armv_contextSwitch_HWASID(vspace_root_t *vspace, asid_t asid)
{
	setCurrentUserVSpaceRoot(ttbr_new(asid, addrFromPPtr(vspace)));
}
/*
 * In AARCH64, hardware and virtual asids are the same and are written
 * when updating the translation table base register.
 */
static inline void armv_contextSwitch(vspace_root_t *vspace, asid_t asid)
{
	setCurrentUserVSpaceRoot(ttbr_new(asid, addrFromPPtr(vspace)));
}
/* The top level asid mapping table */
extern asid_pool_t *armKSASIDTable[(1ul << (asidHighBits))];
/* This is the temporary userspace page table in kernel. It is required before running
 * user thread to avoid speculative page table walking with the wrong page table. */
extern vspace_root_t armKSGlobalUserVSpace[(1ul << (9))];
extern pgde_t armKSGlobalKernelPGD[(1ul << (9))];
extern pude_t armKSGlobalKernelPUD[(1ul << (9))];
extern pde_t armKSGlobalKernelPDs[(1ul << (9))][(1ul << (9))];
extern pte_t armKSGlobalKernelPT[(1ul << (9))];
extern bool_t isFPUEnabledCached[1];
/* Store state in the FPU registers into memory. */
static inline void saveFpuState(user_fpu_state_t *dest)
{
	word_t temp;
	__asm__ volatile(
		/* SIMD and floating-point register file */
		"stp     q0, q1, [%1, #16 * 0]      \n"
		"stp     q2, q3, [%1, #16 * 2]      \n"
		"stp     q4, q5, [%1, #16 * 4]      \n"
		"stp     q6, q7, [%1, #16 * 6]      \n"
		"stp     q8, q9, [%1, #16 * 8]      \n"
		"stp     q10, q11, [%1, #16 * 10]   \n"
		"stp     q12, q13, [%1, #16 * 12]   \n"
		"stp     q14, q15, [%1, #16 * 14]   \n"
		"stp     q16, q17, [%1, #16 * 16]   \n"
		"stp     q18, q19, [%1, #16 * 18]   \n"
		"stp     q20, q21, [%1, #16 * 20]   \n"
		"stp     q22, q23, [%1, #16 * 22]   \n"
		"stp     q24, q25, [%1, #16 * 24]   \n"
		"stp     q26, q27, [%1, #16 * 26]   \n"
		"stp     q28, q29, [%1, #16 * 28]   \n"
		"stp     q30, q31, [%1, #16 * 30]   \n"
		/* FP control and status registers */
		"mrs     %0, fpsr                   \n"
		"str     %w0, [%1, #16 * 32]        \n"
		"mrs     %0, fpcr                   \n"
		"str     %w0, [%1, #16 * 32 + 4]    \n"
		: "=&r"(temp)
		: "r"(dest)
		: "memory");
}
/* Load FPU state from memory into the FPU registers. */
static inline void loadFpuState(user_fpu_state_t *src)
{
	word_t temp;
	__asm__ volatile(
		/* SIMD and floating-point register file */
		"ldp     q0, q1, [%1, #16 * 0]      \n"
		"ldp     q2, q3, [%1, #16 * 2]      \n"
		"ldp     q4, q5, [%1, #16 * 4]      \n"
		"ldp     q6, q7, [%1, #16 * 6]      \n"
		"ldp     q8, q9, [%1, #16 * 8]      \n"
		"ldp     q10, q11, [%1, #16 * 10]   \n"
		"ldp     q12, q13, [%1, #16 * 12]   \n"
		"ldp     q14, q15, [%1, #16 * 14]   \n"
		"ldp     q16, q17, [%1, #16 * 16]   \n"
		"ldp     q18, q19, [%1, #16 * 18]   \n"
		"ldp     q20, q21, [%1, #16 * 20]   \n"
		"ldp     q22, q23, [%1, #16 * 22]   \n"
		"ldp     q24, q25, [%1, #16 * 24]   \n"
		"ldp     q26, q27, [%1, #16 * 26]   \n"
		"ldp     q28, q29, [%1, #16 * 28]   \n"
		"ldp     q30, q31, [%1, #16 * 30]  \n"
		/* FP control and status registers */
		"ldr     %w0, [%1, #16 * 32]        \n"
		"msr     fpsr, %0                   \n"
		"ldr     %w0, [%1, #16 * 32 + 4]    \n"
		"msr     fpcr, %0                   \n"
		: "=&r"(temp)
		: "r"(src)
		: "memory");
}
/* Trap any FPU related instructions to EL2 */
static inline void enableTrapFpu(void)
{
	word_t cptr;
	__asm__ volatile("mrs %x0,"
			 "cptr_el2"
			 : "=r"(cptr));
	cptr |= ((1ul << (10)) | (1ul << (31)));
	do {
		word_t _v = cptr;
		__asm__ volatile("msr "
				 "cptr_el2"
				 ",%x0" ::"r"(_v));
	} while (0);
}
/* Disable trapping FPU instructions to EL2 */
static inline void disableTrapFpu(void)
{
	word_t cptr;
	__asm__ volatile("mrs %x0,"
			 "cptr_el2"
			 : "=r"(cptr));
	cptr &= ~((1ul << (10)) | (1ul << (31)));
	do {
		word_t _v = cptr;
		__asm__ volatile("msr "
				 "cptr_el2"
				 ",%x0" ::"r"(_v));
	} while (0);
}
/* Enable FPU access in EL0 and EL1 */
static inline void enableFpuEL01(void)
{
	word_t cpacr;
	__asm__ volatile("mrs %x0,"
			 "cpacr_el1"
			 : "=r"(cpacr));
	cpacr |= (3 << 20 /* FP regiters access*/);
	do {
		word_t _v = cpacr;
		__asm__ volatile("msr "
				 "cpacr_el1"
				 ",%x0" ::"r"(_v));
	} while (0);
}
/* Disable FPU access in EL0 */
static inline void disableFpuEL0(void)
{
	word_t cpacr;
	__asm__ volatile("mrs %x0,"
			 "cpacr_el1"
			 : "=r"(cpacr));
	cpacr &= ~(3 << 20 /* FP regiters access*/);
	cpacr |= (1 << 20 /* FP regiters access*/);
	do {
		word_t _v = cpacr;
		__asm__ volatile("msr "
				 "cpacr_el1"
				 ",%x0" ::"r"(_v));
	} while (0);
}
/* Enable the FPU to be used without faulting.
 * Required even if the kernel attempts to use the FPU. */
static inline void enableFpu(void)
{
	enableFpuEL01();
	isFPUEnabledCached[0lu] = true;
}
static inline bool_t isFpuEnable(void)
{
	return isFPUEnabledCached[0lu];
}
/* Disable the FPU so that usage of it causes a fault */
static inline void disableFpu(void)
{
	disableFpuEL0();
	isFPUEnabledCached[0lu] = false;
}
bool_t fpsimd_HWCapTest(void);
bool_t fpsimd_init(void);
/* Perform any actions required for the deletion of the given thread. */
void fpuThreadDelete(tcb_t *thread);
/* Handle an FPU exception. */
exception_t handleFPUFault(void);
void switchLocalFpuOwner(user_fpu_state_t *new_owner);
/* Switch the current owner of the FPU state on the core specified by 'cpu'. */
void switchFpuOwner(user_fpu_state_t *new_owner, word_t cpu);
/* Returns whether or not the passed thread is using the current active fpu state */
static inline bool_t nativeThreadUsingFPU(tcb_t *thread)
{
	return &thread->tcbArch.tcbContext.fpuState == ksActiveFPUState;
}
static inline void lazyFPURestore(tcb_t *thread)
{
	if (__builtin_expect(!!(ksActiveFPUState), 0)) {
		/* If we have enabled/disabled the FPU too many times without
		 * someone else trying to use it, we assume it is no longer
		 * in use and switch out its state. */
		if (__builtin_expect(!!(ksFPURestoresSinceSwitch > 64), 0)) {
			switchLocalFpuOwner(NULL);
			ksFPURestoresSinceSwitch = 0;
		} else {
			if (__builtin_expect(!!(nativeThreadUsingFPU(thread)), 1)) {
				/* We are using the FPU, make sure it is enabled */
				enableFpu();
			} else {
				/* Someone is using the FPU and it might be enabled */
				disableFpu();
			}
			ksFPURestoresSinceSwitch++;
		}
	} else {
		/* No-one (including us) is using the FPU, so we assume it
		 * is currently disabled */
	}
}
/* When building the fastpath the assembler in traps.S makes these
 * assumptions. Because compile_asserts are hard to do in assembler,
 * we place them here */
_Static_assert(SysCall == -1, "SysCall_Minus1");
_Static_assert(SysReplyRecv == -2, "SysReplyRecv_Minus2");
/* Use macros to not break verification */
static inline void switchToThread_fp(tcb_t *thread, vspace_root_t *vroot, pde_t stored_hw_asid)
{
	asid_t asid;
	asid = (asid_t)(stored_hw_asid.words[0] & 0xffff);
	armv_contextSwitch_HWASID(vroot, asid);
	ksCurThread = thread;
}
static inline void mdb_node_ptr_mset_mdbNext_mdbRevocable_mdbFirstBadged(mdb_node_t *node_ptr,
									 word_t mdbNext,
									 word_t mdbRevocable,
									 word_t mdbFirstBadged)
{
	node_ptr->words[1] = mdbNext | (mdbRevocable << 1) | mdbFirstBadged;
}
static inline void mdb_node_ptr_set_mdbPrev_np(mdb_node_t *node_ptr, word_t mdbPrev)
{
	node_ptr->words[0] = mdbPrev;
}
static inline bool_t isValidVTableRoot_fp(cap_t vspace_root_cap)
{
	return cap_capType_equals(vspace_root_cap, cap_page_global_directory_cap) &&
	       cap_page_global_directory_cap_get_capPGDIsMapped(vspace_root_cap);
}
/* This is an accelerated check that msgLength, which appears
   in the bottom of the msgInfo word, is <= 4 and that msgExtraCaps
   which appears above it is zero. We are assuming that n_msgRegisters == 4
   for this check to be useful. By masking out the bottom 3 bits, we are
   really checking that n + 3 <= MASK(3), i.e. n + 3 <= 7 or n <= 4. */
_Static_assert(n_msgRegisters == 4, "n_msgRegisters_eq_4");
static inline int fastpath_mi_check(word_t msgInfo)
{
	return (msgInfo & ((1ul << (seL4_MsgLengthBits + seL4_MsgExtraCapBits)) - 1ul)) > 4;
}
static inline void fastpath_copy_mrs(word_t length, tcb_t *src, tcb_t *dest)
{
	word_t i;
	register_t reg;
	/* assuming that length < n_msgRegisters */
	for (i = 0; i < length; i++) {
		/* assuming that the message registers simply increment */
		reg = msgRegisters[0] + i;
		setRegister(dest, reg, getRegister(src, reg));
	}
}
static inline int fastpath_reply_cap_check(cap_t cap)
{
	return cap_capType_equals(cap, cap_reply_cap);
}
/** DONT_TRANSLATE */
static inline void fastpath_restore(word_t badge, word_t msgInfo, tcb_t *cur_thread)
{
	c_exit_hook();
	lazyFPURestore(ksCurThread);
	register word_t badge_reg __asm__("x0") = badge;
	register word_t msgInfo_reg __asm__("x1") = msgInfo;
	register word_t cur_thread_reg __asm__("x2") =
		(word_t)cur_thread->tcbArch.tcbContext.registers;
	__asm__ volatile("mov     sp, x2                     \n"
			 /* Restore thread's SPSR, LR, and SP */
			 "ldp     x21, x22, [sp, %[SP_EL0]]  \n"
			 "ldr     x23, [sp, %[SPSR_EL1]]     \n"
			 "msr     sp_el0, x21                \n"
			 "msr     elr_el1, x22               \n"
			 "msr     spsr_el1, x23              \n"
			 /* Restore remaining registers */
			 "ldp     x2,  x3,  [sp, #16 * 1]    \n"
			 "ldp     x4,  x5,  [sp, #16 * 2]    \n"
			 "ldp     x6,  x7,  [sp, #16 * 3]    \n"
			 "ldp     x8,  x9,  [sp, #16 * 4]    \n"
			 "ldp     x10, x11, [sp, #16 * 5]    \n"
			 "ldp     x12, x13, [sp, #16 * 6]    \n"
			 "ldp     x14, x15, [sp, #16 * 7]    \n"
			 "ldp     x16, x17, [sp, #16 * 8]    \n"
			 "ldp     x18, x19, [sp, #16 * 9]    \n"
			 "ldp     x20, x21, [sp, #16 * 10]   \n"
			 "ldp     x22, x23, [sp, #16 * 11]   \n"
			 "ldp     x24, x25, [sp, #16 * 12]   \n"
			 "ldp     x26, x27, [sp, #16 * 13]   \n"
			 "ldp     x28, x29, [sp, #16 * 14]   \n"
			 "ldr     x30, [sp, %[LR]]           \n"
			 "eret                                 "
			 :
			 : "r"(badge_reg), "r"(msgInfo_reg), "r"(cur_thread_reg),
			   [SP_EL0] "i"((31 * 8)), [SPSR_EL1] "i"((33 * 8)), [LR] "i"((30 * 8))
			 : "memory");
	__builtin_unreachable();
}
void slowpath(syscall_t syscall);
static inline void fastpath_call(word_t cptr, word_t r_msgInfo);
static inline void fastpath_reply_recv(word_t cptr, word_t r_msgInfo);
/** DONT_TRANSLATE */
void restore_user_context(void)
{
	c_exit_hook();
	lazyFPURestore(ksCurThread);
	__asm__ volatile("mov     sp, %0                     \n"
			 /* Restore thread's SPSR, LR, and SP */
			 "ldp     x21, x22, [sp, %[SP_EL0]] \n"
			 "ldr     x23, [sp, %[SPSR_EL1]]    \n"
			 "msr     sp_el0, x21                \n"
			 "msr     elr_el1, x22               \n"
			 "msr     spsr_el1, x23              \n"
			 /* Restore remaining registers */
			 "ldp     x0,  x1,  [sp, #16 * 0]    \n"
			 "ldp     x2,  x3,  [sp, #16 * 1]    \n"
			 "ldp     x4,  x5,  [sp, #16 * 2]    \n"
			 "ldp     x6,  x7,  [sp, #16 * 3]    \n"
			 "ldp     x8,  x9,  [sp, #16 * 4]    \n"
			 "ldp     x10, x11, [sp, #16 * 5]    \n"
			 "ldp     x12, x13, [sp, #16 * 6]    \n"
			 "ldp     x14, x15, [sp, #16 * 7]    \n"
			 "ldp     x16, x17, [sp, #16 * 8]    \n"
			 "ldp     x18, x19, [sp, #16 * 9]    \n"
			 "ldp     x20, x21, [sp, #16 * 10]   \n"
			 "ldp     x22, x23, [sp, #16 * 11]   \n"
			 "ldp     x24, x25, [sp, #16 * 12]   \n"
			 "ldp     x26, x27, [sp, #16 * 13]   \n"
			 "ldp     x28, x29, [sp, #16 * 14]   \n"
			 "ldr     x30, [sp, %[LR]]          \n"
			 "eret"
			 :
			 : "r"(ksCurThread->tcbArch.tcbContext.registers), [SP_EL0] "i"((31 * 8)),
			   [SPSR_EL1] "i"((33 * 8)), [LR] "i"((30 * 8))
			 : "memory");
	__builtin_unreachable();
}
void idle_thread(void)
{
	while (1) {
		wfi();
	}
}
/** DONT_TRANSLATE */
void halt(void)
{
	/* halt is actually, idle thread without the interrupts */
	do {
		word_t _v = ((1 << 9) | (1 << 8) | (1 << 7) | (1 << 6));
		__asm__ volatile("msr "
				 "daif"
				 ",%x0" ::"r"(_v));
	} while (0);
	printf("halting...");
	debug_printKernelEntryReason();
	idle_thread();
	__builtin_unreachable();
}
void Arch_switchToThread(tcb_t *tcb)
{

	setVMRoot(tcb);
}
void Arch_configureIdleThread(tcb_t *tcb)
{
	setRegister(tcb, SPSR_EL1, ((1 << 6) | 5 | 0));
	setRegister(tcb, ELR_EL1, (word_t)&idle_thread);
}
void Arch_switchToIdleThread(void)
{

	setCurrentUserVSpaceRoot(ttbr_new(0, addrFromKPPtr(armKSGlobalUserVSpace)));
}
void Arch_activateIdleThread(tcb_t *tcb)
{
	/* Don't need to do anything */
}
/* caps with fixed slot positions in the root CNode */
enum {
	seL4_CapNull = 0,		/* null cap */
	seL4_CapInitThreadTCB = 1,	/* initial thread's TCB cap */
	seL4_CapInitThreadCNode = 2,	/* initial thread's root CNode cap */
	seL4_CapInitThreadVSpace = 3,	/* initial thread's VSpace cap */
	seL4_CapIRQControl = 4,		/* global IRQ controller cap */
	seL4_CapASIDControl = 5,	/* global ASID controller cap */
	seL4_CapInitThreadASIDPool = 6, /* initial thread's ASID pool cap */
	seL4_CapIOPortControl = 7,	/* global IO port control cap (null cap if not supported) */
	seL4_CapIOSpace = 8,		/* global IO space cap (null cap if no IOMMU support) */
	seL4_CapBootInfoFrame = 9,	/* bootinfo frame cap */
	seL4_CapInitThreadIPCBuffer = 10, /* initial thread's IPC buffer frame cap */
	seL4_CapDomain = 11,		  /* global domain controller cap */
	seL4_CapSMMUSIDControl = 12, /*global SMMU SID controller cap, null cap if not supported*/
	seL4_CapSMMUCBControl = 13,  /*global SMMU CB controller cap, null cap if not supported*/
	seL4_NumInitialCaps = 14
};
/* Legacy code will have assumptions on the vspace root being a Page Directory
 * type, so for now we define one to the other */
/* types */
typedef seL4_Word seL4_SlotPos;
typedef struct seL4_SlotRegion {
	seL4_SlotPos start; /* first CNode slot position OF region */
	seL4_SlotPos end;   /* first CNode slot position AFTER region */
} seL4_SlotRegion;
typedef struct seL4_UntypedDesc {
	seL4_Word paddr;     /* physical address of untyped cap  */
	seL4_Uint8 sizeBits; /* size (2^n) bytes of each untyped */
	seL4_Uint8 isDevice; /* whether the untyped is a device  */
	seL4_Uint8 padding[sizeof(seL4_Word) - 2 * sizeof(seL4_Uint8)];
} seL4_UntypedDesc;
typedef struct seL4_BootInfo {
	seL4_Word extraLen;	      /* length of any additional bootinfo information */
	seL4_NodeId nodeID;	      /* ID [0..numNodes-1] of the seL4 node (0 if uniprocessor) */
	seL4_Word numNodes;	      /* number of seL4 nodes (1 if uniprocessor) */
	seL4_Word numIOPTLevels;      /* number of IOMMU PT levels (0 if no IOMMU support) */
	seL4_IPCBuffer *ipcBuffer;    /* pointer to initial thread's IPC buffer */
	seL4_SlotRegion empty;	      /* empty slots (null caps) */
	seL4_SlotRegion sharedFrames; /* shared-frame caps (shared between seL4 nodes) */
	seL4_SlotRegion userImageFrames; /* userland-image frame caps */
	seL4_SlotRegion userImagePaging; /* userland-image paging structure caps */
	seL4_SlotRegion ioSpaceCaps;	 /* IOSpace caps for ARM SMMU */
	seL4_SlotRegion extraBIPages;	 /* caps for any pages used to back the additional bootinfo
					    information */
	seL4_Word initThreadCNodeSizeBits; /* initial thread's root CNode size (2^n slots) */
	seL4_Domain initThreadDomain;	   /* Initial thread's domain ID */
	seL4_SlotRegion untyped;	   /* untyped-object caps (untyped caps) */
	seL4_UntypedDesc untypedList[230]; /* information about each untyped */
	/* the untypedList should be the last entry in this struct, in order
	 * to make this struct easier to represent in other languages */
} seL4_BootInfo;
/* If extraLen > 0, then 4K after the start of bootinfo there is a region of the
 * size extraLen that contains additional boot info data chunks. They are
 * arch/platform specific and may or may not exist in any given execution. Each
 * chunk has a header that contains an ID to describe the chunk. All IDs share a
 * global namespace to ensure uniqueness.
 */
typedef enum {
	SEL4_BOOTINFO_HEADER_PADDING = 0,
	SEL4_BOOTINFO_HEADER_X86_VBE = 1,
	SEL4_BOOTINFO_HEADER_X86_MBMMAP = 2,
	SEL4_BOOTINFO_HEADER_X86_ACPI_RSDP = 3,
	SEL4_BOOTINFO_HEADER_X86_FRAMEBUFFER = 4,
	SEL4_BOOTINFO_HEADER_X86_TSC_FREQ = 5, /* frequency is in MHz */
	SEL4_BOOTINFO_HEADER_FDT = 6,	       /* device tree */
	/* Add more IDs here, the two elements below must always be at the end. */
	SEL4_BOOTINFO_HEADER_NUM,
	_enum_pad_seL4_BootInfoID = ((1ULL << ((sizeof(long) * 8) - 1)) - 1)
} seL4_BootInfoID;
/* Common header for all additional bootinfo chunks to describe the chunk. */
typedef struct seL4_BootInfoHeader {
	seL4_Word id;  /* identifier of the following blob */
	seL4_Word len; /* length of the chunk, including this header */
} seL4_BootInfoHeader;
typedef int __assert_failed_invalid_seL4_BootInfoHeader
	[(sizeof(seL4_BootInfoHeader) == 2 * sizeof(seL4_Word)) ? 1 : -1];
;
/* declare object-specific macros to hide the casting */
/* The boot info frame takes at least one page, it must be big enough to hold
 * the seL4_BootInfo data structure. Due to internal restrictions, the boot info
 * frame size must be of the form 2^n. Furthermore, there might still be code
 * that makes the hard-coded assumption the boot info frame is always one page.
 */
_Static_assert(sizeof(seL4_BootInfo) <= (1ul << (12)), "bi_size");
/* The max number of free memory regions is:
 * +1 for each available physical memory region (elements in avail_p_regs)
 * +1 for each MODE_RESERVED region, there might be none
 * +1 to allow the kernel to release its own boot data region
 * +1 for a possible gap between ELF images and rootserver objects
 */
/* The regions reserved by the boot code are:
 * +1 for kernel
 * +1 for device tree binary
 * +1 for user image.
 * +1 for each the MODE_RESERVED region, there might be none
 */
/* The maximum number of reserved regions is:
 * +1 for each free memory region (MAX_NUM_FREEMEM_REG)
 * +1 for each kernel frame (NUM_KERNEL_DEVICE_FRAMES, there might be none)
 * +1 for each region reserved by the boot code (NUM_RESERVED_REGIONS)
 */
/*
 * Resolve naming differences between the abstract specifications
 * of the bootstrapping phase and the runtime phase of the kernel.
 */
typedef cte_t slot_t;
typedef cte_t *slot_ptr_t;
/* (node-local) state accessed only during bootstrapping */
typedef struct ndks_boot {
	p_region_t reserved[(((sizeof(avail_p_regs) / sizeof((avail_p_regs)[0])) + 0 + 1 + 1) +
			     (sizeof(kernel_device_frames) / sizeof((kernel_device_frames)[0])) +
			     (3 + 0))];
	word_t resv_count;
	region_t freemem[((sizeof(avail_p_regs) / sizeof((avail_p_regs)[0])) + 0 + 1 + 1)];
	seL4_BootInfo *bi_frame;
	seL4_SlotPos slot_pos_cur;
} ndks_boot_t;
extern ndks_boot_t ndks_boot;
/* function prototypes */
static inline bool_t is_reg_empty(region_t reg)
{
	return reg.start == reg.end;
}
bool_t init_freemem(word_t n_available, const p_region_t *available, word_t n_reserved,
		    const region_t *reserved, v_region_t it_v_reg, word_t extra_bi_size_bits);
bool_t reserve_region(p_region_t reg);
void write_slot(slot_ptr_t slot_ptr, cap_t cap);
cap_t create_root_cnode(void);
bool_t provide_cap(cap_t root_cnode_cap, cap_t cap);
cap_t create_it_asid_pool(cap_t root_cnode_cap);
void write_it_pd_pts(cap_t root_cnode_cap, cap_t it_pd_cap);
bool_t create_idle_thread(void);
bool_t create_untypeds(cap_t root_cnode_cap, region_t boot_mem_reuse_reg);
void bi_finalise(void);
void create_domain_cap(cap_t root_cnode_cap);
cap_t create_ipcbuf_frame_cap(cap_t root_cnode_cap, cap_t pd_cap, vptr_t vptr);
word_t calculate_extra_bi_size_bits(word_t extra_size);
void populate_bi_frame(node_id_t node_id, word_t num_nodes, vptr_t ipcbuf_vptr,
		       word_t extra_bi_size_bits);
void create_bi_frame_cap(cap_t root_cnode_cap, cap_t pd_cap, vptr_t vptr);
typedef struct create_frames_of_region_ret {
	seL4_SlotRegion region;
	bool_t success;
} create_frames_of_region_ret_t;
create_frames_of_region_ret_t create_frames_of_region(cap_t root_cnode_cap, cap_t pd_cap,
						      region_t reg, bool_t do_map,
						      sword_t pv_offset);
cap_t create_it_pd_pts(cap_t root_cnode_cap, v_region_t ui_v_reg, vptr_t ipcbuf_vptr,
		       vptr_t bi_frame_vptr);
tcb_t *create_initial_thread(cap_t root_cnode_cap, cap_t it_pd_cap, vptr_t ui_v_entry,
			     vptr_t bi_frame_vptr, vptr_t ipcbuf_vptr, cap_t ipcbuf_cap);
void init_core_state(tcb_t *scheduler_action);
/* state tracking the memory allocated for root server objects */
typedef struct {
	pptr_t cnode;
	pptr_t vspace;
	pptr_t asid_pool;
	pptr_t ipc_buf;
	pptr_t boot_info;
	pptr_t extra_bi;
	pptr_t tcb;
	region_t paging;
} rootserver_mem_t;
extern rootserver_mem_t rootserver;
/* get the number of paging structures required to cover it_v_reg, with
 * the paging structure covering `bits` of the address range - for a 4k page
 * `bits` would be 12 */
static inline word_t get_n_paging(v_region_t v_reg, word_t bits)
{
	vptr_t start = ROUND_DOWN(v_reg.start, bits);
	vptr_t end = ROUND_UP(v_reg.end, bits);
	return (end - start) / BIT(bits);
}

/* allocate a page table sized structure from rootserver.paging */
static inline pptr_t it_alloc_paging(void)
{
	pptr_t allocated = rootserver.paging.start;
	rootserver.paging.start += (1ul << (12));
	return allocated;
}
/* return the amount of paging structures required to cover v_reg */
word_t arch_get_n_paging(v_region_t it_veg);
/* This header was generated by kernel/tools/invocation_header_gen.py.
 *
 * To add an invocation call number, edit libsel4/include/interfaces/sel4.xml.
 *
 */
enum invocation_label {
	InvalidInvocation,
	UntypedRetype,
	TCBReadRegisters,
	TCBWriteRegisters,
	TCBCopyRegisters,
	TCBConfigure,
	TCBSetPriority,
	TCBSetMCPriority,
	TCBSetSchedParams,
	TCBSetIPCBuffer,
	TCBSetSpace,
	TCBSuspend,
	TCBResume,
	TCBBindNotification,
	TCBUnbindNotification,
	TCBSetTLSBase,
	CNodeRevoke,
	CNodeDelete,
	CNodeCancelBadgedSends,
	CNodeCopy,
	CNodeMint,
	CNodeMove,
	CNodeMutate,
	CNodeRotate,
	CNodeSaveCaller,
	IRQIssueIRQHandler,
	IRQAckIRQ,
	IRQSetIRQHandler,
	IRQClearIRQHandler,
	DomainSetSet,
	nInvocationLabels
};
enum sel4_arch_invocation_label {
	ARMVSpaceClean_Data = nInvocationLabels,
	ARMVSpaceInvalidate_Data,
	ARMVSpaceCleanInvalidate_Data,
	ARMVSpaceUnify_Instruction,
	ARMPageUpperDirectoryMap,
	ARMPageUpperDirectoryUnmap,
	ARMPageDirectoryMap,
	ARMPageDirectoryUnmap,
	nSeL4ArchInvocationLabels
};
enum arch_invocation_label {
	ARMPageTableMap = nSeL4ArchInvocationLabels,
	ARMPageTableUnmap,
	ARMPageMap,
	ARMPageUnmap,
	ARMPageClean_Data,
	ARMPageInvalidate_Data,
	ARMPageCleanInvalidate_Data,
	ARMPageUnify_Instruction,
	ARMPageGetAddress,
	ARMASIDControlMakePool,
	ARMASIDPoolAssign,
	ARMIRQIssueIRQHandlerTrigger,
	nArchInvocationLabels
};
/* define dummy functions */
static inline seL4_SlotRegion create_iospace_caps(cap_t root_cnode_cap)
{
	return (seL4_SlotRegion){.start = 0, .end = 0};
}
static inline exception_t decodeARMIOPTInvocation(word_t invLabel, uint32_t length, cte_t *slot,
						  cap_t cap, word_t *buffer)
{
	return EXCEPTION_NONE;
}
static inline exception_t decodeARMIOMapInvocation(word_t invLabel, uint32_t length, cte_t *slot,
						   cap_t cap, word_t *buffer)
{
	return EXCEPTION_NONE;
}
static inline exception_t performPageInvocationUnmapIO(cap_t cap, cte_t *slot)
{
	return EXCEPTION_NONE;
}
static inline exception_t decodeARMIOSpaceInvocation(word_t invLabel, cap_t cap)
{
	return EXCEPTION_NONE;
}
static inline void unmapIOPage(cap_t cap) {}
static inline void deleteIOPageTable(cap_t cap) {}
static inline void clearIOPageDirectory(cap_t cap) {}
static inline void invalidateTranslationSingleLocal(vptr_t vptr)
{
	invalidateLocalTLB_VAASID(vptr);
}
static inline void invalidateTranslationASIDLocal(hw_asid_t hw_asid)
{
	invalidateLocalTLB_ASID(hw_asid);
}
static inline void invalidateTranslationAllLocal(void)
{
	invalidateLocalTLB();
}
static inline void invalidateTranslationSingle(vptr_t vptr)
{
	invalidateTranslationSingleLocal(vptr);
}
static inline void invalidateTranslationASID(hw_asid_t hw_asid)
{
	invalidateTranslationASIDLocal(hw_asid);
}
static inline void invalidateTranslationAll(void)
{
	invalidateTranslationAllLocal();
}
/*
 * Memory types are defined in Memory Attribute Indirection Register.
 *  - nGnRnE Device non-Gathering, non-Reordering, No Early write acknowledgement
 *  - nGnRE Unused Device non-Gathering, non-Reordering, Early write acknowledgement
 *  - GRE Unused Device Gathering, Reordering, Early write acknowledgement
 *  - NORMAL_NC Normal Memory, Inner/Outer non-cacheable
 *  - NORMAL Normal Memory, Inner/Outer Write-back non-transient, Write-allocate, Read-allocate
 * Note: These should match with contents of MAIR_EL1 register!
 */
enum mair_types { DEVICE_nGnRnE = 0, DEVICE_nGnRE = 1, DEVICE_GRE = 2, NORMAL_NC = 3, NORMAL = 4 };
/* Stage-2 translation memory attributes */
enum mair_s2_types {
	S2_DEVICE_nGnRnE = 0,
	S2_DEVICE_nGnRE = 1,
	S2_DEVICE_nGRE = 2,
	S2_DEVICE_GRE = 3,
	S2_NORMAL_INNER_NC_OUTER_NC = 5,
	S2_NORMAL_INNER_WTC_OUTER_NC = 6,
	S2_NORMAL_INNER_WBC_OUTER_NC = 7,
	S2_NORMAL_INNER_NC_OUTER_WTC = 9,
	S2_NORMAL_INNER_WTC_OUTER_WTC = 10,
	S2_NORMAL_INNER_WBC_OUTER_WTC = 11,
	S2_NORMAL_INNER_NC_OUTER_WBC = 13,
	S2_NORMAL_INNER_WTC_OUTER_WBC = 14,
	S2_NORMAL_INNER_WBC_OUTER_WBC = 15,
	S2_NORMAL = S2_NORMAL_INNER_WBC_OUTER_WBC
};
/* Leif from Linaro said the big.LITTLE clusters should be treated as
 * inner shareable, and we believe so, although the Example B2-1 given in
 * ARM ARM DDI 0487B.b (ID092517) says otherwise.
 */
struct lookupPGDSlot_ret {
	exception_t status;
	pgde_t *pgdSlot;
};
typedef struct lookupPGDSlot_ret lookupPGDSlot_ret_t;
struct lookupPUDSlot_ret {
	exception_t status;
	pude_t *pudSlot;
};
typedef struct lookupPUDSlot_ret lookupPUDSlot_ret_t;
struct lookupPDSlot_ret {
	exception_t status;
	pde_t *pdSlot;
};
typedef struct lookupPDSlot_ret lookupPDSlot_ret_t;
struct lookupPTSlot_ret {
	exception_t status;
	pte_t *ptSlot;
};
typedef struct lookupPTSlot_ret lookupPTSlot_ret_t;
struct lookupFrame_ret {
	paddr_t frameBase;
	vm_page_size_t frameSize;
	bool_t valid;
};
typedef struct lookupFrame_ret lookupFrame_ret_t;
struct findVSpaceForASID_ret {
	exception_t status;
	vspace_root_t *vspace_root;
};
typedef struct findVSpaceForASID_ret findVSpaceForASID_ret_t;
/* Stage-1 access permissions:
 * AP[2:1]  higer EL        EL0
 *   00       rw            None
 *   01       rw            rw
 *   10       r             None
 *   11       r             r
 *
 * Stage-2 access permissions:
 * S2AP    Access from Nonsecure EL1 or Non-secure EL0
 *  00                      None
 *  01                      r
 *  10                      w
 *  11                      rw
 *
 *  For VMs or native seL4 applications, if hypervisor support
 *  is enabled, we use the S2AP. The kernel itself running in
 *  EL2 still uses the Stage-1 AP format.
 */
static word_t APFromVMRights(vm_rights_t vm_rights)
{
	switch (vm_rights) {
	case VMKernelOnly:
		return 0;
	case VMReadWrite:
		return 1;
	case VMKernelReadOnly:
		return 2;
	case VMReadOnly:
		return 3;
	default:
		_fail("Invalid VM rights",
		      "/home/lab/projects/seL4/seL4test/kernel/src/arch/arm/64/kernel/vspace.c",
		      166, __func__);
	}
}
vm_rights_t maskVMRights(vm_rights_t vm_rights, seL4_CapRights_t cap_rights_mask)
{
	if (vm_rights == VMReadOnly && seL4_CapRights_get_capAllowRead(cap_rights_mask)) {
		return VMReadOnly;
	}
	if (vm_rights == VMReadWrite && seL4_CapRights_get_capAllowRead(cap_rights_mask)) {
		if (!seL4_CapRights_get_capAllowWrite(cap_rights_mask)) {
			return VMReadOnly;
		} else {
			return VMReadWrite;
		}
	}
	if (vm_rights == VMReadWrite && !seL4_CapRights_get_capAllowRead(cap_rights_mask) &&
	    seL4_CapRights_get_capAllowWrite(cap_rights_mask)) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "Attempted to make unsupported write only mapping"
			       ">>"
			       "\n",
			       0lu, __func__, 187, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
	}
	return VMKernelOnly;
}
/* ==================== BOOT CODE STARTS HERE ==================== */
/* The 54th bit is defined as UXN (unprivileged execute-never) for stage 1
 * of any tranlsation regime for which stage 1 translation can support
 * two VA ranges. This field applies only to execution at EL0. A value
 * of 0 indicates that this control permits execution.
 *
 * The 54th bit is defined as XN (execute-never) for stage 1 of any translation
 * regime for which the stage 1 translation can support only a singe VA range or
 * stage 2 translation when ARMVv8.2-TTS2UXN is not implemented.
 * This field applies to execution at any exception level to which the stage of
 * translation applies. A value of 0 indicates that this control permits execution.
 *
 * When the kernel is running in EL2, the stage-1 translation only supports one
 * VA range so that the 54th bit is XN. Setting the bit to 0 allows execution.
 *
 */
void map_kernel_frame(paddr_t paddr, pptr_t vaddr, vm_rights_t vm_rights,
		      vm_attributes_t attributes)
{
	word_t uxn = 1; /* unprivileged execute never */
	word_t attr_index;
	word_t shareable;
	if (vm_attributes_get_armPageCacheable(attributes)) {
		attr_index = NORMAL;
		shareable = 0;
	} else {
		attr_index = DEVICE_nGnRnE;
		shareable = 0;
	}
	armKSGlobalKernelPT[(((vaddr) >> ((12))) & ((1ul << (9)) - 1ul))] =
		pte_new(uxn, paddr, 0, /* global */
			1,	       /* access flag */
			shareable, APFromVMRights(vm_rights), attr_index, 3);
}
void map_kernel_window(void)
{
	paddr_t paddr;
	pptr_t vaddr;
	word_t idx;
	/* verify that the kernel window as at the last entry of the PGD */
	/* verify that the kernel device window is 1gb aligned and 1gb in size */
	/* place the PUD into the PGD */
	armKSGlobalKernelPGD[(((PPTR_BASE) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul))] =
		pgde_pgde_pud_new(addrFromKPPtr(armKSGlobalKernelPUD));
	/* place all PDs except the last one in PUD */
	for (idx = (((PPTR_BASE) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul));
	     idx < (((PPTR_TOP) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul)); idx++) {
		armKSGlobalKernelPUD[idx] =
			pude_pude_pd_new(addrFromKPPtr(&armKSGlobalKernelPDs[idx][0]));
	}
	/* map the kernel window using large pages */
	vaddr = PPTR_BASE;
	for (paddr = 0x0ul; paddr < (PPTR_TOP - (PPTR_BASE - 0x0ul)); paddr += (1ul << (21))) {
		armKSGlobalKernelPDs[(((vaddr) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul))][(
			((vaddr) >> (((12) + 9))) & ((1ul << (9)) - 1ul))] =
			pde_pde_large_new(
				1,	  // UXN
				paddr, 0, /* global */
				1,	  /* access flag */
				0,	  /* Inner-shareable if SMP enabled, otherwise unshared */
				0,	  /* VMKernelOnly */
				NORMAL);
		vaddr += (1ul << (21));
	}
	/* put the PD into the PUD for device window */
	armKSGlobalKernelPUD[(((PPTR_TOP) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul))] =
		pude_pude_pd_new(addrFromKPPtr(&armKSGlobalKernelPDs[(1ul << (9)) - 1][0]));
	/* put the PT into the PD for device window */
	armKSGlobalKernelPDs[(1ul << (9)) - 1][(1ul << (9)) - 1] =
		pde_pde_small_new(addrFromKPPtr(armKSGlobalKernelPT));
	map_kernel_devices();
}
/* When the hypervisor support is enabled, the stage-2 translation table format
 * is used for applications.
 * The global bit is always 0.
 * The memory attributes use the S2 translation values.
 */
static void map_it_frame_cap(cap_t vspace_cap, cap_t frame_cap, bool_t executable)
{
	vspace_root_t *vspaceRoot = ((vspace_root_t *)((pptr_t)cap_get_capPtr(vspace_cap)));
	pude_t *pud;
	pde_t *pd;
	pte_t *pt;
	vptr_t vptr = cap_frame_cap_get_capFMappedAddress(frame_cap);
	void *pptr = (void *)cap_frame_cap_get_capFBasePtr(frame_cap);
	vspaceRoot += (((vptr) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul));
	pud = ptrFromPAddr(pgde_pgde_pud_ptr_get_pud_base_address(vspaceRoot));
	pud += (((vptr) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul));
	pd = ptrFromPAddr(pude_pude_pd_ptr_get_pd_base_address(pud));
	pd += (((vptr) >> (((12) + 9))) & ((1ul << (9)) - 1ul));
	pt = ptrFromPAddr(pde_pde_small_ptr_get_pt_base_address(pd));
	*(pt + (((vptr) >> ((12))) & ((1ul << (9)) - 1ul))) =
		pte_new(!executable,	    /* unprivileged execute never */
			addrFromPPtr(pptr), /* page_base_address    */
			1,		    /* not global */
			1,		    /* access flag */
			0,		    /* Inner-shareable if SMP enabled, otherwise unshared */
			APFromVMRights(VMReadWrite), NORMAL, 3);
}
static cap_t create_it_frame_cap(pptr_t pptr, vptr_t vptr, asid_t asid, bool_t use_large)
{
	vm_page_size_t frame_size;
	if (use_large) {
		frame_size = ARMLargePage;
	} else {
		frame_size = ARMSmallPage;
	}
	return cap_frame_cap_new(asid,				/* capFMappedASID */
				 pptr,				/* capFBasePtr */
				 frame_size,			/* capFSize */
				 vptr,				/* capFMappedAddress */
				 wordFromVMRights(VMReadWrite), /* capFVMRights */
				 false				/* capFIsDevice */
	);
}
static void map_it_pt_cap(cap_t vspace_cap, cap_t pt_cap)
{
	vspace_root_t *vspaceRoot = ((vspace_root_t *)((pptr_t)cap_get_capPtr(vspace_cap)));
	pude_t *pud;
	pde_t *pd;
	pte_t *pt = ((pte_t *)(cap_page_table_cap_get_capPTBasePtr(pt_cap)));
	vptr_t vptr = cap_page_table_cap_get_capPTMappedAddress(pt_cap);
	vspaceRoot += (((vptr) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul));
	pud = ptrFromPAddr(pgde_pgde_pud_ptr_get_pud_base_address(vspaceRoot));
	pud += (((vptr) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul));
	pd = ptrFromPAddr(pude_pude_pd_ptr_get_pd_base_address(pud));
	*(pd + (((vptr) >> (((12) + 9))) & ((1ul << (9)) - 1ul))) =
		pde_pde_small_new(addrFromPPtr(pt));
}
static cap_t create_it_pt_cap(cap_t vspace_cap, pptr_t pptr, vptr_t vptr, asid_t asid)
{
	cap_t cap;
	cap = cap_page_table_cap_new(asid, /* capPTMappedASID */
				     pptr, /* capPTBasePtr */
				     1,	   /* capPTIsMapped */
				     vptr  /* capPTMappedAddress */
	);
	map_it_pt_cap(vspace_cap, cap);
	return cap;
}
static void map_it_pd_cap(cap_t vspace_cap, cap_t pd_cap)
{
	vspace_root_t *vspaceRoot = ((vspace_root_t *)((pptr_t)cap_get_capPtr(vspace_cap)));
	pude_t *pud;
	pde_t *pd = ((pde_t *)(cap_page_directory_cap_get_capPDBasePtr(pd_cap)));
	vptr_t vptr = cap_page_directory_cap_get_capPDMappedAddress(pd_cap);
	vspaceRoot += (((vptr) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul));
	pud = ptrFromPAddr(pgde_pgde_pud_ptr_get_pud_base_address(vspaceRoot));
	*(pud + (((vptr) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul))) =
		pude_pude_pd_new(addrFromPPtr(pd));
}
static cap_t create_it_pd_cap(cap_t vspace_cap, pptr_t pptr, vptr_t vptr, asid_t asid)
{
	cap_t cap;
	cap = cap_page_directory_cap_new(asid, /* capPDMappedASID */
					 pptr, /* capPDBasePtr */
					 1,    /* capPDIsMapped */
					 vptr  /* capPDMappedAddress */
	);
	map_it_pd_cap(vspace_cap, cap);
	return cap;
}
static void map_it_pud_cap(cap_t vspace_cap, cap_t pud_cap)
{
	pgde_t *pgd = ((pgde_t *)((pptr_t)cap_get_capPtr(vspace_cap)));
	pude_t *pud = ((pude_t *)(cap_page_upper_directory_cap_get_capPUDBasePtr(pud_cap)));
	vptr_t vptr = cap_page_upper_directory_cap_get_capPUDMappedAddress(pud_cap);
	*(pgd + (((vptr) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul))) =
		pgde_pgde_pud_new(addrFromPPtr(pud));
}
static cap_t create_it_pud_cap(cap_t vspace_cap, pptr_t pptr, vptr_t vptr, asid_t asid)
{
	cap_t cap;
	cap = cap_page_upper_directory_cap_new(asid, /* capPUDMappedASID */
					       pptr, /* capPUDBasePtr */
					       1,    /* capPUDIsMapped */
					       vptr  /* capPUDMappedAddress */
	);
	map_it_pud_cap(vspace_cap, cap);
	return cap;
}
word_t arch_get_n_paging(v_region_t it_v_reg)
{
	return get_n_paging(it_v_reg, PGD_INDEX_OFFSET) + get_n_paging(it_v_reg, PUD_INDEX_OFFSET) +
	       get_n_paging(it_v_reg, PD_INDEX_OFFSET);
}

cap_t create_it_address_space(cap_t root_cnode_cap, v_region_t it_v_reg)
{
	cap_t vspace_cap;
	vptr_t vptr;
	seL4_SlotPos slot_pos_before;
	seL4_SlotPos slot_pos_after;
	/* create the PGD */
	vspace_cap =
		cap_page_global_directory_cap_new(1 /* initial thread's ASID */,
						  /* capPGDMappedASID */ rootserver.vspace,
						  /* capPGDBasePtr   */ 1 /* capPGDIsMapped */);
	slot_pos_before = ndks_boot.slot_pos_cur;
	write_slot((((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) +
		    (seL4_CapInitThreadVSpace)),
		   vspace_cap);
	/* Create any PUDs needed for the user land image */
	for (vptr = (((it_v_reg.start) >> (((((12) + 9) + 9) + 9))) << (((((12) + 9) + 9) + 9)));
	     vptr < it_v_reg.end; vptr += (1ul << (((((12) + 9) + 9) + 9)))) {
		if (!provide_cap(root_cnode_cap,
				 create_it_pud_cap(vspace_cap, it_alloc_paging(), vptr,
						   1 /* initial thread's ASID */))) {
			return cap_null_cap_new();
		}
	}
	/* Create any PDs needed for the user land image */
	for (vptr = (((it_v_reg.start) >> ((((12) + 9) + 9))) << ((((12) + 9) + 9)));
	     vptr < it_v_reg.end; vptr += (1ul << ((((12) + 9) + 9)))) {
		if (!provide_cap(root_cnode_cap,
				 create_it_pd_cap(vspace_cap, it_alloc_paging(), vptr,
						  1 /* initial thread's ASID */))) {
			return cap_null_cap_new();
		}
	}
	/* Create any PTs needed for the user land image */
	for (vptr = (((it_v_reg.start) >> (((12) + 9))) << (((12) + 9))); vptr < it_v_reg.end;
	     vptr += (1ul << (((12) + 9)))) {
		if (!provide_cap(root_cnode_cap,
				 create_it_pt_cap(vspace_cap, it_alloc_paging(), vptr,
						  1 /* initial thread's ASID */))) {
			return cap_null_cap_new();
		}
	}
	slot_pos_after = ndks_boot.slot_pos_cur;
	ndks_boot.bi_frame->userImagePaging = (seL4_SlotRegion){slot_pos_before, slot_pos_after};
	return vspace_cap;
}
cap_t create_unmapped_it_frame_cap(pptr_t pptr, bool_t use_large)
{
	return create_it_frame_cap(pptr, 0, asidInvalid, use_large);
}
cap_t create_mapped_it_frame_cap(cap_t pd_cap, pptr_t pptr, vptr_t vptr, asid_t asid,
				 bool_t use_large, bool_t executable)
{
	cap_t cap = create_it_frame_cap(pptr, vptr, asid, use_large);
	map_it_frame_cap(pd_cap, cap, executable);
	return cap;
}
void activate_kernel_vspace(void)
{
	cleanInvalidateL1Caches();
	setCurrentKernelVSpaceRoot(ttbr_new(0, addrFromKPPtr(armKSGlobalKernelPGD)));
	/* Prevent elf-loader address translation to fill up TLB */
	setCurrentUserVSpaceRoot(ttbr_new(0, addrFromKPPtr(armKSGlobalUserVSpace)));
	invalidateLocalTLB();
	lockTLBEntry(KERNEL_ELF_BASE);
}
void write_it_asid_pool(cap_t it_ap_cap, cap_t it_vspace_cap)
{
	asid_pool_t *ap = ((asid_pool_t *)(pptr_t)cap_get_capPtr(it_ap_cap));
	asid_map_t asid_map = asid_map_asid_map_vspace_new(
		/* vspace_root: reference to vspace root page table object */
		(word_t)((
			pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(it_vspace_cap))));
	ap->array[1 /* initial thread's ASID */] = asid_map;
	armKSASIDTable[1 /* initial thread's ASID */ >> asidLowBits] = ap;
}
/* ==================== BOOT CODE FINISHES HERE ==================== */
asid_map_t findMapForASID(asid_t asid)
{
	asid_pool_t *poolPtr;
	poolPtr = armKSASIDTable[asid >> asidLowBits];
	if (!poolPtr) {
		return asid_map_asid_map_none_new();
	}
	return poolPtr->array[asid & ((1ul << (asidLowBits)) - 1ul)];
}
static findVSpaceForASID_ret_t findVSpaceForASID(asid_t asid)
{
	findVSpaceForASID_ret_t ret;
	asid_map_t asid_map;
	asid_map = findMapForASID(asid);
	if (asid_map_get_type(asid_map) != asid_map_asid_map_vspace) {
		current_lookup_fault = lookup_fault_invalid_root_new();
		ret.vspace_root = NULL;
		ret.status = EXCEPTION_LOOKUP_FAULT;
		return ret;
	}
	ret.vspace_root = (vspace_root_t *)asid_map_asid_map_vspace_get_vspace_root(asid_map);
	ret.status = EXCEPTION_NONE;
	return ret;
}
word_t *lookupIPCBuffer(bool_t isReceiver, tcb_t *thread)
{
	word_t w_bufferPtr;
	cap_t bufferCap;
	vm_rights_t vm_rights;
	w_bufferPtr = thread->tcbIPCBuffer;
	bufferCap = (((cte_t *)((word_t)(thread) & ~((1ul << (11)) - 1ul))) + (tcbBuffer))->cap;
	if (cap_get_capType(bufferCap) != cap_frame_cap) {
		return NULL;
	}
	if (cap_frame_cap_get_capFIsDevice(bufferCap)) {
		return NULL;
	}
	vm_rights = cap_frame_cap_get_capFVMRights(bufferCap);
	if (vm_rights == VMReadWrite || (!isReceiver && vm_rights == VMReadOnly)) {
		word_t basePtr;
		unsigned int pageBits;
		basePtr = cap_frame_cap_get_capFBasePtr(bufferCap);
		pageBits = pageBitsForSize(cap_frame_cap_get_capFSize(bufferCap));
		return (word_t *)(basePtr + (w_bufferPtr & ((1ul << (pageBits)) - 1ul)));
	} else {
		return NULL;
	}
}
exception_t checkValidIPCBuffer(vptr_t vptr, cap_t cap)
{
	if (cap_get_capType(cap) != cap_frame_cap) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "IPC Buffer is an invalid cap."
			       ">>"
			       "\n",
			       0lu, __func__, 636, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (__builtin_expect(!!(cap_frame_cap_get_capFIsDevice(cap)), 0)) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "Specifying a device frame as an IPC buffer is not permitted."
			       ">>"
			       "\n",
			       0lu, __func__, 642, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (!(!((vptr) & ((1ul << (10)) - 1ul)))) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "IPC Buffer vaddr 0x%x is not aligned."
			       ">>"
			       "\n",
			       0lu, __func__, 648, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), (int)vptr);
		} while (0);
		current_syscall_error.type = seL4_AlignmentError;
		return EXCEPTION_SYSCALL_ERROR;
	}
	return EXCEPTION_NONE;
}
static lookupPGDSlot_ret_t lookupPGDSlot(vspace_root_t *vspace, vptr_t vptr)
{
	lookupPGDSlot_ret_t ret;
	pgde_t *pgd = ((pgde_t *)(vspace));
	word_t pgdIndex = (((vptr) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul));
	ret.status = EXCEPTION_NONE;
	ret.pgdSlot = pgd + pgdIndex;
	return ret;
}
static lookupPUDSlot_ret_t lookupPUDSlot(vspace_root_t *vspace, vptr_t vptr)
{
	lookupPUDSlot_ret_t ret;
	lookupPGDSlot_ret_t pgdSlot = lookupPGDSlot(vspace, vptr);
	if (!pgde_pgde_pud_ptr_get_present(pgdSlot.pgdSlot)) {
		current_lookup_fault = lookup_fault_missing_capability_new(((((12) + 9) + 9) + 9));
		ret.pudSlot = NULL;
		ret.status = EXCEPTION_LOOKUP_FAULT;
		return ret;
	} else {
		pude_t *pud;
		pude_t *pudSlot;
		word_t pudIndex = (((vptr) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul));
		pud = ptrFromPAddr(pgde_pgde_pud_ptr_get_pud_base_address(pgdSlot.pgdSlot));
		pudSlot = pud + pudIndex;
		ret.status = EXCEPTION_NONE;
		ret.pudSlot = pudSlot;
		return ret;
	}
}
static lookupPDSlot_ret_t lookupPDSlot(vspace_root_t *vspace, vptr_t vptr)
{
	lookupPUDSlot_ret_t pudSlot;
	lookupPDSlot_ret_t ret;
	pudSlot = lookupPUDSlot(vspace, vptr);
	if (pudSlot.status != EXCEPTION_NONE) {
		ret.pdSlot = NULL;
		ret.status = pudSlot.status;
		return ret;
	}
	if (!pude_pude_pd_ptr_get_present(pudSlot.pudSlot)) {
		current_lookup_fault = lookup_fault_missing_capability_new((((12) + 9) + 9));
		ret.pdSlot = NULL;
		ret.status = EXCEPTION_LOOKUP_FAULT;
		return ret;
	} else {
		pde_t *pd;
		pde_t *pdSlot;
		word_t pdIndex = (((vptr) >> (((12) + 9))) & ((1ul << (9)) - 1ul));
		pd = ptrFromPAddr(pude_pude_pd_ptr_get_pd_base_address(pudSlot.pudSlot));
		pdSlot = pd + pdIndex;
		ret.status = EXCEPTION_NONE;
		ret.pdSlot = pdSlot;
		return ret;
	}
}
static lookupPTSlot_ret_t lookupPTSlot(vspace_root_t *vspace, vptr_t vptr)
{
	lookupPTSlot_ret_t ret;
	lookupPDSlot_ret_t pdSlot;
	pdSlot = lookupPDSlot(vspace, vptr);
	if (pdSlot.status != EXCEPTION_NONE) {
		ret.ptSlot = NULL;
		ret.status = pdSlot.status;
		return ret;
	}
	if (!pde_pde_small_ptr_get_present(pdSlot.pdSlot)) {
		current_lookup_fault = lookup_fault_missing_capability_new(((12) + 9));
		ret.ptSlot = NULL;
		ret.status = EXCEPTION_LOOKUP_FAULT;
		return ret;
	} else {
		pte_t *pt;
		pte_t *ptSlot;
		word_t ptIndex = (((vptr) >> ((12))) & ((1ul << (9)) - 1ul));
		pt = ptrFromPAddr(pde_pde_small_ptr_get_pt_base_address(pdSlot.pdSlot));
		ptSlot = pt + ptIndex;
		ret.ptSlot = ptSlot;
		ret.status = EXCEPTION_NONE;
		return ret;
	}
}
static lookupFrame_ret_t lookupFrame(vspace_root_t *vspace, vptr_t vptr)
{
	lookupPUDSlot_ret_t pudSlot;
	lookupFrame_ret_t ret;
	pudSlot = lookupPUDSlot(vspace, vptr);
	if (pudSlot.status != EXCEPTION_NONE) {
		ret.valid = false;
		return ret;
	}
	switch (pude_ptr_get_pude_type(pudSlot.pudSlot)) {
	case pude_pude_1g:
		ret.frameBase = pude_pude_1g_ptr_get_page_base_address(pudSlot.pudSlot);
		ret.frameSize = ARMHugePage;
		ret.valid = true;
		return ret;
	case pude_pude_pd: {
		pde_t *pd = ptrFromPAddr(pude_pude_pd_ptr_get_pd_base_address(pudSlot.pudSlot));
		pde_t *pdSlot = pd + (((vptr) >> (((12) + 9))) & ((1ul << (9)) - 1ul));
		if (pde_ptr_get_pde_type(pdSlot) == pde_pde_large) {
			ret.frameBase = pde_pde_large_ptr_get_page_base_address(pdSlot);
			ret.frameSize = ARMLargePage;
			ret.valid = true;
			return ret;
		}
		if (pde_ptr_get_pde_type(pdSlot) == pde_pde_small) {
			pte_t *pt = ptrFromPAddr(pde_pde_small_ptr_get_pt_base_address(pdSlot));
			pte_t *ptSlot = pt + (((vptr) >> ((12))) & ((1ul << (9)) - 1ul));
			if (pte_ptr_get_present(ptSlot)) {
				ret.frameBase = pte_ptr_get_page_base_address(ptSlot);
				ret.frameSize = ARMSmallPage;
				ret.valid = true;
				return ret;
			}
		}
	}
	}
	ret.valid = false;
	return ret;
}
/* Note that if the hypervisor support is enabled, the user page tables use
 * stage-2 translation format. Otherwise, they follow the stage-1 translation format.
 */
static pte_t makeUser3rdLevel(paddr_t paddr, vm_rights_t vm_rights, vm_attributes_t attributes)
{
	bool_t nonexecutable = vm_attributes_get_armExecuteNever(attributes);
	if (vm_attributes_get_armPageCacheable(attributes)) {
		return pte_new(nonexecutable, /* unprivileged execute never */
			       paddr, 1,      /* not global */
			       1,	      /* access flag */
			       0, /* Inner-shareable if SMP enabled, otherwise unshared */
			       APFromVMRights(vm_rights), NORMAL, 3);
	} else {
		return pte_new(nonexecutable, /* unprivileged execute never */
			       paddr, 1,      /* not global */
			       1,	      /* access flag */
			       0,	      /* Ignored - Outter shareable */
			       APFromVMRights(vm_rights), DEVICE_nGnRnE, 3);
	}
}
static pde_t makeUser2ndLevel(paddr_t paddr, vm_rights_t vm_rights, vm_attributes_t attributes)
{
	bool_t nonexecutable = vm_attributes_get_armExecuteNever(attributes);
	if (vm_attributes_get_armPageCacheable(attributes)) {
		return pde_pde_large_new(nonexecutable, /* unprivileged execute never */
					 paddr, 1,	/* not global */
					 1,		/* access flag */
					 0, /* Inner-shareable if SMP enabled, otherwise unshared */
					 APFromVMRights(vm_rights), NORMAL);
	} else {
		return pde_pde_large_new(nonexecutable, /* unprivileged execute never */
					 paddr, 1,	/* not global */
					 1,		/* access flag */
					 0,		/* Ignored - Outter shareable */
					 APFromVMRights(vm_rights), DEVICE_nGnRnE);
	}
}
static pude_t makeUser1stLevel(paddr_t paddr, vm_rights_t vm_rights, vm_attributes_t attributes)
{
	bool_t nonexecutable = vm_attributes_get_armExecuteNever(attributes);
	if (vm_attributes_get_armPageCacheable(attributes)) {
		return pude_pude_1g_new(nonexecutable, /* unprivileged execute never */
					paddr, 1,      /* not global */
					1,	       /* access flag */
					0, /* Inner-shareable if SMP enabled, otherwise unshared */
					APFromVMRights(vm_rights), NORMAL);
	} else {
		return pude_pude_1g_new(nonexecutable, /* unprivileged execute never */
					paddr, 1,      /* not global */
					1,	       /* access flag */
					0,	       /* Ignored - Outter shareable */
					APFromVMRights(vm_rights), DEVICE_nGnRnE);
	}
}
exception_t handleVMFault(tcb_t *thread, vm_fault_type_t vm_faultType)
{
	switch (vm_faultType) {
	case ARMDataAbort: {
		word_t addr, fault;
		addr = getFAR();
		fault = getESR();
		current_fault = seL4_Fault_VMFault_new(addr, fault, false);
		return EXCEPTION_FAULT;
	}
	case ARMPrefetchAbort: {
		word_t pc, fault;
		pc = getRestartPC(thread);
		fault = getESR();
		current_fault = seL4_Fault_VMFault_new(pc, fault, true);
		return EXCEPTION_FAULT;
	}
	default:
		_fail("Invalid VM fault type",
		      "/home/lab/projects/seL4/seL4test/kernel/src/arch/arm/64/kernel/vspace.c",
		      979, __func__);
	}
}
bool_t isVTableRoot(cap_t cap)
{
	return cap_get_capType(cap) == cap_page_global_directory_cap;
}
bool_t isValidNativeRoot(cap_t cap)
{
	return isVTableRoot(cap) && cap_page_global_directory_cap_get_capPGDIsMapped(cap);
}
bool_t isValidVTableRoot(cap_t cap)
{
	return isValidNativeRoot(cap);
}
void setVMRoot(tcb_t *tcb)
{
	cap_t threadRoot;
	asid_t asid;
	vspace_root_t *vspaceRoot;
	findVSpaceForASID_ret_t find_ret;
	threadRoot = (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap;
	if (!isValidNativeRoot(threadRoot)) {
		setCurrentUserVSpaceRoot(ttbr_new(0, addrFromKPPtr(armKSGlobalUserVSpace)));
		return;
	}
	vspaceRoot = ((vspace_root_t *)((
		(pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(threadRoot)))));
	asid = cap_page_global_directory_cap_get_capPGDMappedASID(threadRoot);
	find_ret = findVSpaceForASID(asid);
	if (__builtin_expect(
		    !!(find_ret.status != EXCEPTION_NONE || find_ret.vspace_root != vspaceRoot),
		    0)) {
		setCurrentUserVSpaceRoot(ttbr_new(0, addrFromKPPtr(armKSGlobalUserVSpace)));
		return;
	}
	armv_contextSwitch(vspaceRoot, asid);
}
static bool_t setVMRootForFlush(vspace_root_t *vspace, asid_t asid)
{
	cap_t threadRoot;
	threadRoot =
		(((cte_t *)((word_t)(ksCurThread) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap;
	if (cap_get_capType(threadRoot) == cap_page_global_directory_cap &&
	    cap_page_global_directory_cap_get_capPGDIsMapped(threadRoot) &&
	    ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(threadRoot))) == vspace) {
		return false;
	}
	armv_contextSwitch(vspace, asid);
	return true;
}
pgde_t *pageUpperDirectoryMapped(asid_t asid, vptr_t vaddr, pude_t *pud)
{
	findVSpaceForASID_ret_t find_ret;
	lookupPGDSlot_ret_t lu_ret;
	find_ret = findVSpaceForASID(asid);
	if (find_ret.status != EXCEPTION_NONE) {
		return NULL;
	}
	lu_ret = lookupPGDSlot(find_ret.vspace_root, vaddr);
	if (pgde_pgde_pud_ptr_get_present(lu_ret.pgdSlot) &&
	    (pgde_pgde_pud_ptr_get_pud_base_address(lu_ret.pgdSlot) == addrFromPPtr(pud))) {
		return lu_ret.pgdSlot;
	}
	return NULL;
}
pude_t *pageDirectoryMapped(asid_t asid, vptr_t vaddr, pde_t *pd)
{
	findVSpaceForASID_ret_t find_ret;
	lookupPUDSlot_ret_t lu_ret;
	find_ret = findVSpaceForASID(asid);
	if (find_ret.status != EXCEPTION_NONE) {
		return NULL;
	}
	lu_ret = lookupPUDSlot(find_ret.vspace_root, vaddr);
	if (lu_ret.status != EXCEPTION_NONE) {
		return NULL;
	}
	if (pude_pude_pd_ptr_get_present(lu_ret.pudSlot) &&
	    (pude_pude_pd_ptr_get_pd_base_address(lu_ret.pudSlot) == addrFromPPtr(pd))) {
		return lu_ret.pudSlot;
	}
	return NULL;
}
static inline void invalidateTLBByASID(asid_t asid)
{
	invalidateTranslationASID(asid);
}
static inline void invalidateTLBByASIDVA(asid_t asid, vptr_t vaddr)
{
	invalidateTranslationSingle((asid << 48) | vaddr >> 12);
}
pde_t *pageTableMapped(asid_t asid, vptr_t vaddr, pte_t *pt)
{
	findVSpaceForASID_ret_t find_ret;
	lookupPDSlot_ret_t lu_ret;
	find_ret = findVSpaceForASID(asid);
	if (find_ret.status != EXCEPTION_NONE) {
		return NULL;
	}
	lu_ret = lookupPDSlot(find_ret.vspace_root, vaddr);
	if (lu_ret.status != EXCEPTION_NONE) {
		return NULL;
	}
	if (pde_pde_small_ptr_get_present(lu_ret.pdSlot) &&
	    (pde_pde_small_ptr_get_pt_base_address(lu_ret.pdSlot) == addrFromPPtr(pt))) {
		return lu_ret.pdSlot;
	}
	return NULL;
}
void unmapPageUpperDirectory(asid_t asid, vptr_t vaddr, pude_t *pud)
{
	pgde_t *pgdSlot;
	pgdSlot = pageUpperDirectoryMapped(asid, vaddr, pud);
	if (pgdSlot != NULL) {
		*pgdSlot = pgde_pgde_invalid_new();
		cleanByVA_PoU((vptr_t)pgdSlot, addrFromPPtr(pgdSlot));
		invalidateTLBByASID(asid);
	}
}
void unmapPageDirectory(asid_t asid, vptr_t vaddr, pde_t *pd)
{
	pude_t *pudSlot;
	pudSlot = pageDirectoryMapped(asid, vaddr, pd);
	if (pudSlot != NULL) {
		*pudSlot = pude_invalid_new();
		cleanByVA_PoU((vptr_t)pudSlot, addrFromPPtr(pudSlot));
		invalidateTLBByASID(asid);
	}
}
void unmapPageTable(asid_t asid, vptr_t vaddr, pte_t *pt)
{
	pde_t *pdSlot;
	pdSlot = pageTableMapped(asid, vaddr, pt);
	if (pdSlot != NULL) {
		*pdSlot = pde_invalid_new();
		cleanByVA_PoU((vptr_t)pdSlot, addrFromPPtr(pdSlot));
		invalidateTLBByASID(asid);
	}
}
void unmapPage(vm_page_size_t page_size, asid_t asid, vptr_t vptr, pptr_t pptr)
{
	paddr_t addr;
	findVSpaceForASID_ret_t find_ret;
	addr = addrFromPPtr((void *)pptr);
	find_ret = findVSpaceForASID(asid);
	if (find_ret.status != EXCEPTION_NONE) {
		return;
	}
	switch (page_size) {
	case ARMSmallPage: {
		lookupPTSlot_ret_t lu_ret;
		lu_ret = lookupPTSlot(find_ret.vspace_root, vptr);
		if (lu_ret.status != EXCEPTION_NONE) {
			return;
		}
		if (pte_ptr_get_present(lu_ret.ptSlot) &&
		    pte_ptr_get_page_base_address(lu_ret.ptSlot) == addr) {
			*(lu_ret.ptSlot) = pte_invalid_new();
			cleanByVA_PoU((vptr_t)lu_ret.ptSlot, addrFromPPtr(lu_ret.ptSlot));
		}
		break;
	}
	case ARMLargePage: {
		lookupPDSlot_ret_t lu_ret;
		lu_ret = lookupPDSlot(find_ret.vspace_root, vptr);
		if (lu_ret.status != EXCEPTION_NONE) {
			return;
		}
		if (pde_pde_large_ptr_get_present(lu_ret.pdSlot) &&
		    pde_pde_large_ptr_get_page_base_address(lu_ret.pdSlot) == addr) {
			*(lu_ret.pdSlot) = pde_invalid_new();
			cleanByVA_PoU((vptr_t)lu_ret.pdSlot, addrFromPPtr(lu_ret.pdSlot));
		}
		break;
	}
	case ARMHugePage: {
		lookupPUDSlot_ret_t lu_ret;
		lu_ret = lookupPUDSlot(find_ret.vspace_root, vptr);
		if (lu_ret.status != EXCEPTION_NONE) {
			return;
		}
		if (pude_pude_1g_ptr_get_present(lu_ret.pudSlot) &&
		    pude_pude_1g_ptr_get_page_base_address(lu_ret.pudSlot) == addr) {
			*(lu_ret.pudSlot) = pude_invalid_new();
			cleanByVA_PoU((vptr_t)lu_ret.pudSlot, addrFromPPtr(lu_ret.pudSlot));
		}
		break;
	}
	default:
		_fail("Invalid ARM page type",
		      "/home/lab/projects/seL4/seL4test/kernel/src/arch/arm/64/kernel/vspace.c",
		      1387, __func__);
	}
	invalidateTLBByASIDVA(asid, vptr);
}
void deleteASID(asid_t asid, vspace_root_t *vspace)
{
	asid_pool_t *poolPtr;
	poolPtr = armKSASIDTable[asid >> asidLowBits];
	if (poolPtr != NULL) {
		asid_map_t asid_map = poolPtr->array[asid & ((1ul << (asidLowBits)) - 1ul)];
		if (asid_map_get_type(asid_map) == asid_map_asid_map_vspace &&
		    (vspace_root_t *)asid_map_asid_map_vspace_get_vspace_root(asid_map) == vspace) {
			invalidateTLBByASID(asid);
			poolPtr->array[asid & ((1ul << (asidLowBits)) - 1ul)] =
				asid_map_asid_map_none_new();
			setVMRoot(ksCurThread);
		}
	}
}
void deleteASIDPool(asid_t asid_base, asid_pool_t *pool)
{
	word_t offset;
	if (armKSASIDTable[asid_base >> asidLowBits] == pool) {
		for (offset = 0; offset < (1ul << (asidLowBits)); offset++) {
			asid_map_t asid_map = pool->array[offset];
			if (asid_map_get_type(asid_map) == asid_map_asid_map_vspace) {
				invalidateTLBByASID(asid_base + offset);
			}
		}
		armKSASIDTable[asid_base >> asidLowBits] = NULL;
		setVMRoot(ksCurThread);
	}
}
static void doFlush(int invLabel, vptr_t start, vptr_t end, paddr_t pstart)
{
	switch (invLabel) {
	case ARMVSpaceClean_Data:
	case ARMPageClean_Data:
		cleanCacheRange_RAM(start, end, pstart);
		break;
	case ARMVSpaceInvalidate_Data:
	case ARMPageInvalidate_Data:
		invalidateCacheRange_RAM(start, end, pstart);
		break;
	case ARMVSpaceCleanInvalidate_Data:
	case ARMPageCleanInvalidate_Data:
		cleanInvalidateCacheRange_RAM(start, end, pstart);
		break;
	case ARMVSpaceUnify_Instruction:
	case ARMPageUnify_Instruction:
		/* First clean data lines to point of unification... */
		cleanCacheRange_PoU(start, end, pstart);
		/* Ensure it's been written. */
		dsb();
		/* ...then invalidate the corresponding instruction lines
		   to point of unification... */
		invalidateCacheRange_I(start, end, pstart);
		/* ... and ensure new instructions come from fresh cache lines. */
		isb();
		break;
	default:
		_fail("Invalid operation, shouldn't get here.\n",
		      "/home/lab/projects/seL4/seL4test/kernel/src/arch/arm/64/kernel/vspace.c",
		      1466, __func__);
	}
}
/* ================= INVOCATION HANDLING STARTS HERE ================== */
static exception_t performVSpaceFlush(int invLabel, vspace_root_t *vspaceRoot, asid_t asid,
				      vptr_t start, vptr_t end, paddr_t pstart)
{
	bool_t root_switched;
	/* Flush if given a non zero range */
	if (start < end) {
		root_switched = setVMRootForFlush(vspaceRoot, asid);
		doFlush(invLabel, start, end, pstart);
		if (root_switched) {
			setVMRoot(ksCurThread);
		}
	}
	return EXCEPTION_NONE;
}
static exception_t performUpperPageDirectoryInvocationMap(cap_t cap, cte_t *ctSlot, pgde_t pgde,
							  pgde_t *pgdSlot)
{
	ctSlot->cap = cap;
	*pgdSlot = pgde;
	cleanByVA_PoU((vptr_t)pgdSlot, addrFromPPtr(pgdSlot));
	return EXCEPTION_NONE;
}
static exception_t performUpperPageDirectoryInvocationUnmap(cap_t cap, cte_t *ctSlot)
{
	if (cap_page_upper_directory_cap_get_capPUDIsMapped(cap)) {
		pude_t *pud = ((pude_t *)(cap_page_upper_directory_cap_get_capPUDBasePtr(cap)));
		unmapPageUpperDirectory(cap_page_upper_directory_cap_get_capPUDMappedASID(cap),
					cap_page_upper_directory_cap_get_capPUDMappedAddress(cap),
					pud);
		clearMemory_PT((void *)pud, cap_get_capSizeBits(cap));
	}
	cap_page_upper_directory_cap_ptr_set_capPUDIsMapped(&(ctSlot->cap), 0);
	return EXCEPTION_NONE;
}
static exception_t performPageDirectoryInvocationMap(cap_t cap, cte_t *ctSlot, pude_t pude,
						     pude_t *pudSlot)
{
	ctSlot->cap = cap;
	*pudSlot = pude;
	cleanByVA_PoU((vptr_t)pudSlot, addrFromPPtr(pudSlot));
	return EXCEPTION_NONE;
}
static exception_t performPageDirectoryInvocationUnmap(cap_t cap, cte_t *ctSlot)
{
	if (cap_page_directory_cap_get_capPDIsMapped(cap)) {
		pde_t *pd = ((pde_t *)(cap_page_directory_cap_get_capPDBasePtr(cap)));
		unmapPageDirectory(cap_page_directory_cap_get_capPDMappedASID(cap),
				   cap_page_directory_cap_get_capPDMappedAddress(cap), pd);
		clearMemory_PT((void *)pd, cap_get_capSizeBits(cap));
	}
	cap_page_directory_cap_ptr_set_capPDIsMapped(&(ctSlot->cap), 0);
	return EXCEPTION_NONE;
}
static exception_t performPageTableInvocationMap(cap_t cap, cte_t *ctSlot, pde_t pde, pde_t *pdSlot)
{
	ctSlot->cap = cap;
	*pdSlot = pde;
	cleanByVA_PoU((vptr_t)pdSlot, addrFromPPtr(pdSlot));
	return EXCEPTION_NONE;
}
static exception_t performPageTableInvocationUnmap(cap_t cap, cte_t *ctSlot)
{
	if (cap_page_table_cap_get_capPTIsMapped(cap)) {
		pte_t *pt = ((pte_t *)(cap_page_table_cap_get_capPTBasePtr(cap)));
		unmapPageTable(cap_page_table_cap_get_capPTMappedASID(cap),
			       cap_page_table_cap_get_capPTMappedAddress(cap), pt);
		clearMemory_PT((void *)pt, cap_get_capSizeBits(cap));
	}
	cap_page_table_cap_ptr_set_capPTIsMapped(&(ctSlot->cap), 0);
	return EXCEPTION_NONE;
}
static exception_t performHugePageInvocationMap(asid_t asid, cap_t cap, cte_t *ctSlot, pude_t pude,
						pude_t *pudSlot)
{
	bool_t tlbflush_required = pude_pude_1g_ptr_get_present(pudSlot);
	ctSlot->cap = cap;
	*pudSlot = pude;
	cleanByVA_PoU((vptr_t)pudSlot, addrFromPPtr(pudSlot));
	if (__builtin_expect(!!(tlbflush_required), 0)) {
		invalidateTLBByASIDVA(asid, cap_frame_cap_get_capFMappedAddress(cap));
	}
	return EXCEPTION_NONE;
}
static exception_t performLargePageInvocationMap(asid_t asid, cap_t cap, cte_t *ctSlot, pde_t pde,
						 pde_t *pdSlot)
{
	bool_t tlbflush_required = pde_pde_large_ptr_get_present(pdSlot);
	ctSlot->cap = cap;
	*pdSlot = pde;
	cleanByVA_PoU((vptr_t)pdSlot, addrFromPPtr(pdSlot));
	if (__builtin_expect(!!(tlbflush_required), 0)) {
		invalidateTLBByASIDVA(asid, cap_frame_cap_get_capFMappedAddress(cap));
	}
	return EXCEPTION_NONE;
}
static exception_t performSmallPageInvocationMap(asid_t asid, cap_t cap, cte_t *ctSlot, pte_t pte,
						 pte_t *ptSlot)
{
	bool_t tlbflush_required = pte_ptr_get_present(ptSlot);
	ctSlot->cap = cap;
	*ptSlot = pte;
	cleanByVA_PoU((vptr_t)ptSlot, addrFromPPtr(ptSlot));
	if (__builtin_expect(!!(tlbflush_required), 0)) {
		invalidateTLBByASIDVA(asid, cap_frame_cap_get_capFMappedAddress(cap));
	}
	return EXCEPTION_NONE;
}
static exception_t performPageInvocationUnmap(cap_t cap, cte_t *ctSlot)
{
	if (cap_frame_cap_get_capFMappedASID(cap) != 0) {
		unmapPage(cap_frame_cap_get_capFSize(cap), cap_frame_cap_get_capFMappedASID(cap),
			  cap_frame_cap_get_capFMappedAddress(cap),
			  cap_frame_cap_get_capFBasePtr(cap));
	}
	cap_frame_cap_ptr_set_capFMappedASID(&ctSlot->cap, asidInvalid);
	cap_frame_cap_ptr_set_capFMappedAddress(&ctSlot->cap, 0);
	return EXCEPTION_NONE;
}
static exception_t performPageFlush(int invLabel, vspace_root_t *vspaceRoot, asid_t asid,
				    vptr_t start, vptr_t end, paddr_t pstart)
{
	bool_t root_switched;
	if (start < end) {
		root_switched = setVMRootForFlush(vspaceRoot, asid);
		doFlush(invLabel, start, end, pstart);
		if (root_switched) {
			setVMRoot(ksCurThread);
		}
	}
	return EXCEPTION_NONE;
}
static exception_t performPageGetAddress(pptr_t base_ptr)
{
	paddr_t base = addrFromPPtr((void *)base_ptr);
	setRegister(ksCurThread, msgRegisters[0], base);
	setRegister(ksCurThread, msgInfoRegister,
		    wordFromMessageInfo(seL4_MessageInfo_new(0, 0, 0, 1)));
	return EXCEPTION_NONE;
}
static exception_t performASIDControlInvocation(void *frame, cte_t *slot, cte_t *parent,
						asid_t asid_base)
{
	cap_untyped_cap_ptr_set_capFreeIndex(
		&(parent->cap), ((1ul << ((cap_untyped_cap_get_capBlockSize(parent->cap)) - 4))));
	memzero(frame, (1ul << (12)));
	cteInsert(cap_asid_pool_cap_new(asid_base,	  /* capASIDBase  */
					((word_t)(frame)) /* capASIDPool  */
					),
		  parent, slot);
	armKSASIDTable[asid_base >> asidLowBits] = (asid_pool_t *)frame;
	return EXCEPTION_NONE;
}
static exception_t decodeARMVSpaceRootInvocation(word_t invLabel, unsigned int length, cte_t *cte,
						 cap_t cap, word_t *buffer)
{
	vptr_t start, end;
	paddr_t pstart;
	asid_t asid;
	vspace_root_t *vspaceRoot;
	lookupFrame_ret_t resolve_ret;
	findVSpaceForASID_ret_t find_ret;
	switch (invLabel) {
	case ARMVSpaceClean_Data:
	case ARMVSpaceInvalidate_Data:
	case ARMVSpaceCleanInvalidate_Data:
	case ARMVSpaceUnify_Instruction:
		if (length < 2) {
			do {
				printf("<<"
				       "seL4(CPU %"
				       "lu"
				       ")"
				       " [%s/%d T%p \"%s\" @%lx]: "
				       "VSpaceRoot Flush: Truncated message."
				       ">>"
				       "\n",
				       0lu, __func__, 1709, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_TruncatedMessage;
			return EXCEPTION_SYSCALL_ERROR;
		}
		start = getSyscallArg(0, buffer);
		end = getSyscallArg(1, buffer);
		/* Check sanity of arguments */
		if (end <= start) {
			do {
				printf("<<"
				       "seL4(CPU %"
				       "lu"
				       ")"
				       " [%s/%d T%p \"%s\" @%lx]: "
				       "VSpaceRoot Flush: Invalid range."
				       ">>"
				       "\n",
				       0lu, __func__, 1719, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_InvalidArgument;
			current_syscall_error.invalidArgumentNumber = 1;
			return EXCEPTION_SYSCALL_ERROR;
		}
		/* Don't let applications flush kernel regions. */
		if (end > 0x00007fffffffffff) {
			do {
				printf("<<"
				       "seL4(CPU %"
				       "lu"
				       ")"
				       " [%s/%d T%p \"%s\" @%lx]: "
				       "VSpaceRoot Flush: Exceed the user addressable region."
				       ">>"
				       "\n",
				       0lu, __func__, 1727, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_IllegalOperation;
			return EXCEPTION_SYSCALL_ERROR;
		}
		if (__builtin_expect(!!(!isValidNativeRoot(cap)), 0)) {
			current_syscall_error.type = seL4_InvalidCapability;
			current_syscall_error.invalidCapNumber = 0;
			return EXCEPTION_SYSCALL_ERROR;
		}
		/* Make sure that the supplied pgd is ok */
		vspaceRoot = ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(cap)));
		asid = cap_page_global_directory_cap_get_capPGDMappedASID(cap);
		find_ret = findVSpaceForASID(asid);
		if (__builtin_expect(!!(find_ret.status != EXCEPTION_NONE), 0)) {
			do {
				printf("<<"
				       "seL4(CPU %"
				       "lu"
				       ")"
				       " [%s/%d T%p \"%s\" @%lx]: "
				       "VSpaceRoot Flush: No VSpace for ASID"
				       ">>"
				       "\n",
				       0lu, __func__, 1744, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_FailedLookup;
			current_syscall_error.failedLookupWasSource = false;
			return EXCEPTION_SYSCALL_ERROR;
		}
		if (__builtin_expect(!!(find_ret.vspace_root != vspaceRoot), 0)) {
			do {
				printf("<<"
				       "seL4(CPU %"
				       "lu"
				       ")"
				       " [%s/%d T%p \"%s\" @%lx]: "
				       "VSpaceRoot Flush: Invalid VSpace Cap"
				       ">>"
				       "\n",
				       0lu, __func__, 1751, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_InvalidCapability;
			current_syscall_error.invalidCapNumber = 0;
			return EXCEPTION_SYSCALL_ERROR;
		}
		/* Look up the frame containing 'start'. */
		resolve_ret = lookupFrame(vspaceRoot, start);
		if (!resolve_ret.valid) {
			/* Fail silently, as there can't be any stale cached data (for the
			 * given address space), and getting a syscall error because the
			 * relevant page is non-resident would be 'astonishing'. */
			setThreadState(ksCurThread, ThreadState_Restart);
			return EXCEPTION_NONE;
		}
		/* Refuse to cross a page boundary. */
		if (((start) & ~((1ul << (pageBitsForSize((resolve_ret.frameSize)))) - 1ul)) !=
		    ((end - 1) & ~((1ul << (pageBitsForSize((resolve_ret.frameSize)))) - 1ul))) {
			current_syscall_error.type = seL4_RangeError;
			current_syscall_error.rangeErrorMin = start;
			current_syscall_error.rangeErrorMax =
				((start) &
				 ~((1ul << (pageBitsForSize((resolve_ret.frameSize)))) - 1ul)) +
				((1ul << (pageBitsForSize(resolve_ret.frameSize))) - 1ul);
			return EXCEPTION_SYSCALL_ERROR;
		}
		/* Calculate the physical start address. */
		pstart = resolve_ret.frameBase +
			 ((start) & ((1ul << (pageBitsForSize((resolve_ret.frameSize)))) - 1ul));
		setThreadState(ksCurThread, ThreadState_Restart);
		return performVSpaceFlush(invLabel, vspaceRoot, asid, start, end - 1, pstart);
	default:
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
}
static exception_t decodeARMPageUpperDirectoryInvocation(word_t invLabel, unsigned int length,
							 cte_t *cte, cap_t cap, word_t *buffer)
{
	cap_t pgdCap;
	vspace_root_t *pgd;
	pgde_t pgde;
	asid_t asid;
	vptr_t vaddr;
	lookupPGDSlot_ret_t pgdSlot;
	findVSpaceForASID_ret_t find_ret;
	if (invLabel == ARMPageUpperDirectoryUnmap) {
		if (!isFinalCapability(cte)) {
			current_syscall_error.type = seL4_RevokeFirst;
			return EXCEPTION_SYSCALL_ERROR;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return performUpperPageDirectoryInvocationUnmap(cap, cte);
	}
	if (invLabel != ARMPageUpperDirectoryMap) {
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (length < 2 || current_extra_caps.excaprefs[0] == NULL) {
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (cap_page_upper_directory_cap_get_capPUDIsMapped(cap)) {
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 0;
		return EXCEPTION_SYSCALL_ERROR;
	}
	vaddr = getSyscallArg(0, buffer) & (~((1ul << (((((12) + 9) + 9) + 9))) - 1ul));
	pgdCap = current_extra_caps.excaprefs[0]->cap;
	if (!isValidNativeRoot(pgdCap)) {
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	pgd = ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(pgdCap)));
	asid = cap_page_global_directory_cap_get_capPGDMappedASID(pgdCap);
	if (vaddr > 0x00007fffffffffff) {
		current_syscall_error.type = seL4_InvalidArgument;
		current_syscall_error.invalidArgumentNumber = 0;
		return EXCEPTION_SYSCALL_ERROR;
	}
	find_ret = findVSpaceForASID(asid);
	if (find_ret.status != EXCEPTION_NONE) {
		current_syscall_error.type = seL4_FailedLookup;
		current_syscall_error.failedLookupWasSource = false;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (find_ret.vspace_root != pgd) {
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	pgdSlot = lookupPGDSlot(pgd, vaddr);
	if (pgde_pgde_pud_ptr_get_present(pgdSlot.pgdSlot)) {
		current_syscall_error.type = seL4_DeleteFirst;
		return EXCEPTION_SYSCALL_ERROR;
	}
	pgde = pgde_pgde_pud_new(
		addrFromPPtr(((pude_t *)(cap_page_upper_directory_cap_get_capPUDBasePtr(cap)))));
	cap_page_upper_directory_cap_ptr_set_capPUDIsMapped(&cap, 1);
	cap_page_upper_directory_cap_ptr_set_capPUDMappedASID(&cap, asid);
	cap_page_upper_directory_cap_ptr_set_capPUDMappedAddress(&cap, vaddr);
	setThreadState(ksCurThread, ThreadState_Restart);
	return performUpperPageDirectoryInvocationMap(cap, cte, pgde, pgdSlot.pgdSlot);
}
static exception_t decodeARMPageDirectoryInvocation(word_t invLabel, unsigned int length,
						    cte_t *cte, cap_t cap, word_t *buffer)
{
	cap_t vspaceRootCap;
	vspace_root_t *vspaceRoot;
	pude_t pude;
	asid_t asid;
	vptr_t vaddr;
	lookupPUDSlot_ret_t pudSlot;
	findVSpaceForASID_ret_t find_ret;
	if (invLabel == ARMPageDirectoryUnmap) {
		if (__builtin_expect(!!(!isFinalCapability(cte)), 0)) {
			current_syscall_error.type = seL4_RevokeFirst;
			return EXCEPTION_SYSCALL_ERROR;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return performPageDirectoryInvocationUnmap(cap, cte);
	}
	if (__builtin_expect(!!(invLabel != ARMPageDirectoryMap), 0)) {
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (__builtin_expect(!!(length < 2 || current_extra_caps.excaprefs[0] == NULL), 0)) {
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (__builtin_expect(!!(cap_page_directory_cap_get_capPDIsMapped(cap)), 0)) {
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 0;
		return EXCEPTION_SYSCALL_ERROR;
	}
	vaddr = getSyscallArg(0, buffer) & (~((1ul << ((((12) + 9) + 9))) - 1ul));
	vspaceRootCap = current_extra_caps.excaprefs[0]->cap;
	if (__builtin_expect(!!(!isValidNativeRoot(vspaceRootCap)), 0)) {
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	vspaceRoot = ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(vspaceRootCap)));
	asid = cap_page_global_directory_cap_get_capPGDMappedASID(vspaceRootCap);
	if (__builtin_expect(!!(vaddr > 0x00007fffffffffff), 0)) {
		current_syscall_error.type = seL4_InvalidArgument;
		current_syscall_error.invalidArgumentNumber = 0;
		return EXCEPTION_SYSCALL_ERROR;
	}
	find_ret = findVSpaceForASID(asid);
	if (__builtin_expect(!!(find_ret.status != EXCEPTION_NONE), 0)) {
		current_syscall_error.type = seL4_FailedLookup;
		current_syscall_error.failedLookupWasSource = false;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (__builtin_expect(!!(find_ret.vspace_root != vspaceRoot), 0)) {
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	pudSlot = lookupPUDSlot(vspaceRoot, vaddr);
	if (pudSlot.status != EXCEPTION_NONE) {
		current_syscall_error.type = seL4_FailedLookup;
		current_syscall_error.failedLookupWasSource = false;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (__builtin_expect(!!(pude_pude_pd_ptr_get_present(pudSlot.pudSlot) ||
				pude_pude_1g_ptr_get_present(pudSlot.pudSlot)),
			     0)) {
		current_syscall_error.type = seL4_DeleteFirst;
		return EXCEPTION_SYSCALL_ERROR;
	}
	pude = pude_pude_pd_new(
		addrFromPPtr(((pde_t *)(cap_page_directory_cap_get_capPDBasePtr(cap)))));
	cap_page_directory_cap_ptr_set_capPDIsMapped(&cap, 1);
	cap_page_directory_cap_ptr_set_capPDMappedASID(&cap, asid);
	cap_page_directory_cap_ptr_set_capPDMappedAddress(&cap, vaddr);
	setThreadState(ksCurThread, ThreadState_Restart);
	return performPageDirectoryInvocationMap(cap, cte, pude, pudSlot.pudSlot);
}
static exception_t decodeARMPageTableInvocation(word_t invLabel, unsigned int length, cte_t *cte,
						cap_t cap, word_t *buffer)
{
	cap_t vspaceRootCap;
	vspace_root_t *vspaceRoot;
	pde_t pde;
	asid_t asid;
	vptr_t vaddr;
	lookupPDSlot_ret_t pdSlot;
	findVSpaceForASID_ret_t find_ret;
	if (invLabel == ARMPageTableUnmap) {
		if (__builtin_expect(!!(!isFinalCapability(cte)), 0)) {
			current_syscall_error.type = seL4_RevokeFirst;
			return EXCEPTION_SYSCALL_ERROR;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return performPageTableInvocationUnmap(cap, cte);
	}
	if (invLabel != ARMPageTableMap) {
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (length < 2 || current_extra_caps.excaprefs[0] == NULL) {
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (cap_page_table_cap_get_capPTIsMapped(cap)) {
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 0;
		return EXCEPTION_SYSCALL_ERROR;
	}
	vaddr = getSyscallArg(0, buffer) & (~((1ul << (((12) + 9))) - 1ul));
	vspaceRootCap = current_extra_caps.excaprefs[0]->cap;
	if (!isValidNativeRoot(vspaceRootCap)) {
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	vspaceRoot = ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(vspaceRootCap)));
	asid = cap_page_global_directory_cap_get_capPGDMappedASID(vspaceRootCap);
	if (vaddr > 0x00007fffffffffff) {
		current_syscall_error.type = seL4_InvalidArgument;
		current_syscall_error.invalidArgumentNumber = 0;
		return EXCEPTION_SYSCALL_ERROR;
	}
	find_ret = findVSpaceForASID(asid);
	if (find_ret.status != EXCEPTION_NONE) {
		current_syscall_error.type = seL4_FailedLookup;
		current_syscall_error.failedLookupWasSource = false;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (find_ret.vspace_root != vspaceRoot) {
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	pdSlot = lookupPDSlot(vspaceRoot, vaddr);
	if (pdSlot.status != EXCEPTION_NONE) {
		current_syscall_error.type = seL4_FailedLookup;
		current_syscall_error.failedLookupWasSource = false;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (pde_pde_small_ptr_get_present(pdSlot.pdSlot) ||
	    pde_pde_large_ptr_get_present(pdSlot.pdSlot)) {
		current_syscall_error.type = seL4_DeleteFirst;
		return EXCEPTION_SYSCALL_ERROR;
	}
	pde = pde_pde_small_new(
		addrFromPPtr(((pte_t *)(cap_page_table_cap_get_capPTBasePtr(cap)))));
	cap_page_table_cap_ptr_set_capPTIsMapped(&cap, 1);
	cap_page_table_cap_ptr_set_capPTMappedASID(&cap, asid);
	cap_page_table_cap_ptr_set_capPTMappedAddress(&cap, vaddr);
	setThreadState(ksCurThread, ThreadState_Restart);
	return performPageTableInvocationMap(cap, cte, pde, pdSlot.pdSlot);
}
static exception_t decodeARMFrameInvocation(word_t invLabel, unsigned int length, cte_t *cte,
					    cap_t cap, word_t *buffer)
{
	switch (invLabel) {
	case ARMPageMap: {
		vptr_t vaddr;
		paddr_t base;
		cap_t vspaceRootCap;
		vspace_root_t *vspaceRoot;
		asid_t asid, frame_asid;
		vm_rights_t vmRights;
		vm_page_size_t frameSize;
		vm_attributes_t attributes;
		findVSpaceForASID_ret_t find_ret;
		if (length < 3 || current_extra_caps.excaprefs[0] == NULL) {
			current_syscall_error.type = seL4_TruncatedMessage;
			return EXCEPTION_SYSCALL_ERROR;
		}
		vaddr = getSyscallArg(0, buffer);
		attributes = vmAttributesFromWord(getSyscallArg(2, buffer));
		vspaceRootCap = current_extra_caps.excaprefs[0]->cap;
		frameSize = cap_frame_cap_get_capFSize(cap);
		vmRights = maskVMRights(cap_frame_cap_get_capFVMRights(cap),
					rightsFromWord(getSyscallArg(1, buffer)));
		if (!isValidNativeRoot(vspaceRootCap)) {
			current_syscall_error.type = seL4_InvalidCapability;
			current_syscall_error.invalidCapNumber = 1;
			return EXCEPTION_SYSCALL_ERROR;
		}
		vspaceRoot = ((
			pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(vspaceRootCap)));
		asid = cap_page_global_directory_cap_get_capPGDMappedASID(vspaceRootCap);
		find_ret = findVSpaceForASID(asid);
		if (find_ret.status != EXCEPTION_NONE) {
			current_syscall_error.type = seL4_FailedLookup;
			current_syscall_error.failedLookupWasSource = false;
			return EXCEPTION_SYSCALL_ERROR;
		}
		if (find_ret.vspace_root != vspaceRoot) {
			current_syscall_error.type = seL4_InvalidCapability;
			current_syscall_error.invalidCapNumber = 1;
			return EXCEPTION_SYSCALL_ERROR;
		}
		if (!(((vaddr) & ((1ul << (pageBitsForSize((frameSize)))) - 1ul)) == 0)) {
			current_syscall_error.type = seL4_AlignmentError;
			return EXCEPTION_SYSCALL_ERROR;
		}
		/* In the case of remap, the cap should have a valid asid */
		frame_asid = cap_frame_cap_ptr_get_capFMappedASID(&cap);
		if (frame_asid != asidInvalid) {
			if (frame_asid != asid) {
				do {
					printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: "
					       "ARMPageMap: Attempting to remap a frame that does "
					       "not belong to the passed address space>>\n",
					       0lu, __func__, 2121, ksCurThread,
					       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
									   ~((1ul << (11)) -
									     1ul))) +
								(tcbCNodeEntries)))
						       ->tcbName,
					       (word_t)getRestartPC(ksCurThread));
				} while (0);
				current_syscall_error.type = seL4_InvalidCapability;
				current_syscall_error.invalidArgumentNumber = 0;
				return EXCEPTION_SYSCALL_ERROR;
			} else if (cap_frame_cap_get_capFMappedAddress(cap) != vaddr) {
				do {
					printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: "
					       "ARMPageMap: Attempting to map frame into multiple "
					       "addresses>>\n",
					       0lu, __func__, 2127, ksCurThread,
					       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
									   ~((1ul << (11)) -
									     1ul))) +
								(tcbCNodeEntries)))
						       ->tcbName,
					       (word_t)getRestartPC(ksCurThread));
				} while (0);
				current_syscall_error.type = seL4_InvalidArgument;
				current_syscall_error.invalidArgumentNumber = 2;
				return EXCEPTION_SYSCALL_ERROR;
			}
		} else {
			if (vaddr + (1ul << (pageBitsForSize(frameSize))) - 1 >
			    0x00007fffffffffff) {
				current_syscall_error.type = seL4_InvalidArgument;
				current_syscall_error.invalidArgumentNumber = 0;
				return EXCEPTION_SYSCALL_ERROR;
			}
		}
		cap = cap_frame_cap_set_capFMappedASID(cap, asid);
		cap = cap_frame_cap_set_capFMappedAddress(cap, vaddr);
		base = addrFromPPtr((void *)cap_frame_cap_get_capFBasePtr(cap));
		if (frameSize == ARMSmallPage) {
			lookupPTSlot_ret_t lu_ret = lookupPTSlot(vspaceRoot, vaddr);
			if (lu_ret.status != EXCEPTION_NONE) {
				current_syscall_error.type = seL4_FailedLookup;
				current_syscall_error.failedLookupWasSource = false;
				return EXCEPTION_SYSCALL_ERROR;
			}
			setThreadState(ksCurThread, ThreadState_Restart);
			return performSmallPageInvocationMap(
				asid, cap, cte, makeUser3rdLevel(base, vmRights, attributes),
				lu_ret.ptSlot);
		} else if (frameSize == ARMLargePage) {
			lookupPDSlot_ret_t lu_ret = lookupPDSlot(vspaceRoot, vaddr);
			if (lu_ret.status != EXCEPTION_NONE) {
				current_syscall_error.type = seL4_FailedLookup;
				current_syscall_error.failedLookupWasSource = false;
				return EXCEPTION_SYSCALL_ERROR;
			}
			setThreadState(ksCurThread, ThreadState_Restart);
			return performLargePageInvocationMap(
				asid, cap, cte, makeUser2ndLevel(base, vmRights, attributes),
				lu_ret.pdSlot);
		} else {
			lookupPUDSlot_ret_t lu_ret = lookupPUDSlot(vspaceRoot, vaddr);
			if (lu_ret.status != EXCEPTION_NONE) {
				current_syscall_error.type = seL4_FailedLookup;
				current_syscall_error.failedLookupWasSource = false;
				return EXCEPTION_SYSCALL_ERROR;
			}
			setThreadState(ksCurThread, ThreadState_Restart);
			return performHugePageInvocationMap(
				asid, cap, cte, makeUser1stLevel(base, vmRights, attributes),
				lu_ret.pudSlot);
		}
	}
	case ARMPageUnmap:
		setThreadState(ksCurThread, ThreadState_Restart);
		return performPageInvocationUnmap(cap, cte);
	case ARMPageClean_Data:
	case ARMPageInvalidate_Data:
	case ARMPageCleanInvalidate_Data:
	case ARMPageUnify_Instruction: {
		vptr_t start, end;
		vptr_t vaddr;
		asid_t asid;
		word_t page_size;
		findVSpaceForASID_ret_t find_ret;
		if (length < 2) {
			do {
				printf("<<"
				       "seL4(CPU %"
				       "lu"
				       ")"
				       " [%s/%d T%p \"%s\" @%lx]: "
				       "Page Flush: Truncated message."
				       ">>"
				       "\n",
				       0lu, __func__, 2201, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_TruncatedMessage;
			return EXCEPTION_SYSCALL_ERROR;
		}
		if (__builtin_expect(!!(cap_frame_cap_get_capFMappedASID(cap) == 0), 0)) {
			do {
				printf("<<"
				       "seL4(CPU %"
				       "lu"
				       ")"
				       " [%s/%d T%p \"%s\" @%lx]: "
				       "Page Flush: Frame is not mapped."
				       ">>"
				       "\n",
				       0lu, __func__, 2207, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_IllegalOperation;
			return EXCEPTION_SYSCALL_ERROR;
		}
		vaddr = cap_frame_cap_get_capFMappedAddress(cap);
		asid = cap_frame_cap_get_capFMappedASID(cap);
		find_ret = findVSpaceForASID(asid);
		if (__builtin_expect(!!(find_ret.status != EXCEPTION_NONE), 0)) {
			do {
				printf("<<"
				       "seL4(CPU %"
				       "lu"
				       ")"
				       " [%s/%d T%p \"%s\" @%lx]: "
				       "Page Flush: No PGD for ASID"
				       ">>"
				       "\n",
				       0lu, __func__, 2217, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_FailedLookup;
			current_syscall_error.failedLookupWasSource = false;
			return EXCEPTION_SYSCALL_ERROR;
		}
		start = getSyscallArg(0, buffer);
		end = getSyscallArg(1, buffer);
		/* check that the range is sane */
		if (end <= start) {
			do {
				printf("<<"
				       "seL4(CPU %"
				       "lu"
				       ")"
				       " [%s/%d T%p \"%s\" @%lx]: "
				       "PageFlush: Invalid range"
				       ">>"
				       "\n",
				       0lu, __func__, 2228, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_InvalidArgument;
			current_syscall_error.invalidArgumentNumber = 1;
			return EXCEPTION_SYSCALL_ERROR;
		}
		/* start and end are currently relative inside this page */
		page_size = (1ul << (pageBitsForSize(cap_frame_cap_get_capFSize(cap))));
		if (start >= page_size || end > page_size) {
			do {
				printf("<<"
				       "seL4(CPU %"
				       "lu"
				       ")"
				       " [%s/%d T%p \"%s\" @%lx]: "
				       "Page Flush: Requested range not inside page"
				       ">>"
				       "\n",
				       0lu, __func__, 2237, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_InvalidArgument;
			current_syscall_error.invalidArgumentNumber = 0;
			return EXCEPTION_SYSCALL_ERROR;
		}
		word_t pstart = addrFromPPtr((void *)cap_frame_cap_get_capFBasePtr(cap)) + start;
		setThreadState(ksCurThread, ThreadState_Restart);
		return performPageFlush(invLabel, find_ret.vspace_root, asid, vaddr + start,
					vaddr + end - 1, pstart);
	}
	case ARMPageGetAddress:
		setThreadState(ksCurThread, ThreadState_Restart);
		return performPageGetAddress(cap_frame_cap_get_capFBasePtr(cap));
	default:
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
}
exception_t decodeARMMMUInvocation(word_t invLabel, word_t length, cptr_t cptr, cte_t *cte,
				   cap_t cap, word_t *buffer)
{
	switch (cap_get_capType(cap)) {
	case cap_page_global_directory_cap:
		return decodeARMVSpaceRootInvocation(invLabel, length, cte, cap, buffer);
	case cap_page_upper_directory_cap:
		return decodeARMPageUpperDirectoryInvocation(invLabel, length, cte, cap, buffer);
	case cap_page_directory_cap:
		return decodeARMPageDirectoryInvocation(invLabel, length, cte, cap, buffer);
	case cap_page_table_cap:
		return decodeARMPageTableInvocation(invLabel, length, cte, cap, buffer);
	case cap_frame_cap:
		return decodeARMFrameInvocation(invLabel, length, cte, cap, buffer);
	case cap_asid_control_cap: {
		unsigned int i;
		asid_t asid_base;
		word_t index, depth;
		cap_t untyped, root;
		cte_t *parentSlot, *destSlot;
		lookupSlot_ret_t lu_ret;
		void *frame;
		exception_t status;
		if (__builtin_expect(!!(invLabel != ARMASIDControlMakePool), 0)) {
			current_syscall_error.type = seL4_IllegalOperation;
			return EXCEPTION_SYSCALL_ERROR;
		}
		if (__builtin_expect(!!(length < 2 || current_extra_caps.excaprefs[0] == NULL ||
					current_extra_caps.excaprefs[1] == NULL),
				     0)) {
			current_syscall_error.type = seL4_TruncatedMessage;
			return EXCEPTION_SYSCALL_ERROR;
		}
		index = getSyscallArg(0, buffer);
		depth = getSyscallArg(1, buffer);
		parentSlot = current_extra_caps.excaprefs[0];
		untyped = parentSlot->cap;
		root = current_extra_caps.excaprefs[1]->cap;
		/* Find first free pool */
		for (i = 0; i < (1ul << (asidHighBits)) && armKSASIDTable[i]; i++)
			;
		if (__builtin_expect(!!(i == (1ul << (asidHighBits))),
				     0)) { /* If no unallocated pool is found */
			current_syscall_error.type = seL4_DeleteFirst;
			return EXCEPTION_SYSCALL_ERROR;
		}
		asid_base = i << asidLowBits;
		if (__builtin_expect(!!(cap_get_capType(untyped) != cap_untyped_cap ||
					cap_untyped_cap_get_capBlockSize(untyped) != 12 ||
					cap_untyped_cap_get_capIsDevice(untyped)),
				     0)) {
			current_syscall_error.type = seL4_InvalidCapability;
			current_syscall_error.invalidCapNumber = 1;
			return EXCEPTION_SYSCALL_ERROR;
		}
		status = ensureNoChildren(parentSlot);
		if (__builtin_expect(!!(status != EXCEPTION_NONE), 0)) {
			return status;
		}
		frame = ((word_t *)(cap_untyped_cap_get_capPtr(untyped)));
		lu_ret = lookupTargetSlot(root, index, depth);
		if (__builtin_expect(!!(lu_ret.status != EXCEPTION_NONE), 0)) {
			return lu_ret.status;
		}
		destSlot = lu_ret.slot;
		status = ensureEmptySlot(destSlot);
		if (__builtin_expect(!!(status != EXCEPTION_NONE), 0)) {
			return status;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return performASIDControlInvocation(frame, destSlot, parentSlot, asid_base);
	}
	case cap_asid_pool_cap: {
		cap_t vspaceCap;
		cte_t *vspaceCapSlot;
		asid_pool_t *pool;
		unsigned int i;
		asid_t asid;
		if (__builtin_expect(!!(invLabel != ARMASIDPoolAssign), 0)) {
			current_syscall_error.type = seL4_IllegalOperation;
			return EXCEPTION_SYSCALL_ERROR;
		}
		if (__builtin_expect(!!(current_extra_caps.excaprefs[0] == NULL), 0)) {
			current_syscall_error.type = seL4_TruncatedMessage;
			return EXCEPTION_SYSCALL_ERROR;
		}
		vspaceCapSlot = current_extra_caps.excaprefs[0];
		vspaceCap = vspaceCapSlot->cap;
		if (__builtin_expect(
			    !!(!isVTableRoot(vspaceCap) ||
			       cap_page_global_directory_cap_get_capPGDIsMapped(vspaceCap)),
			    0)) {
			current_syscall_error.type = seL4_InvalidCapability;
			current_syscall_error.invalidCapNumber = 1;
			return EXCEPTION_SYSCALL_ERROR;
		}
		pool = armKSASIDTable[cap_asid_pool_cap_get_capASIDBase(cap) >> asidLowBits];
		if (__builtin_expect(!!(!pool), 0)) {
			current_syscall_error.type = seL4_FailedLookup;
			current_syscall_error.failedLookupWasSource = false;
			current_lookup_fault = lookup_fault_invalid_root_new();
			return EXCEPTION_SYSCALL_ERROR;
		}
		if (__builtin_expect(
			    !!(pool != ((asid_pool_t *)cap_asid_pool_cap_get_capASIDPool(cap))),
			    0)) {
			current_syscall_error.type = seL4_InvalidCapability;
			current_syscall_error.invalidCapNumber = 0;
			return EXCEPTION_SYSCALL_ERROR;
		}
		/* Find first free ASID */
		asid = cap_asid_pool_cap_get_capASIDBase(cap);
		for (i = 0; i < (1 << asidLowBits) &&
			    (asid + i == 0 ||
			     (asid_map_get_type(pool->array[i]) != asid_map_asid_map_none));
		     i++)
			;
		if (__builtin_expect(!!(i == 1 << asidLowBits), 0)) {
			current_syscall_error.type = seL4_DeleteFirst;
			return EXCEPTION_SYSCALL_ERROR;
		}
		asid += i;
		setThreadState(ksCurThread, ThreadState_Restart);
		return performASIDPoolInvocation(asid, pool, vspaceCapSlot);
	}
	default:
		_fail("Invalid ARM arch cap type",
		      "/home/lab/projects/seL4/seL4test/kernel/src/arch/arm/64/kernel/vspace.c",
		      2423, __func__);
	}
}
void kernelPrefetchAbort(word_t pc);
void kernelDataAbort(word_t pc);
void kernelPrefetchAbort(word_t pc)
{
	printf("\n\nKERNEL PREFETCH ABORT!\n");
	printf("Faulting instruction: 0x%"
	       "lx"
	       "\n",
	       pc);
	printf("ESR (IFSR): 0x%"
	       "lx"
	       "\n",
	       getESR());
	halt();
}
void kernelDataAbort(word_t pc)
{
	printf("\n\nKERNEL DATA ABORT!\n");
	printf("Faulting instruction: 0x%"
	       "lx"
	       "\n",
	       pc);
	printf("FAR: 0x%"
	       "lx"
	       " ESR (DFSR): 0x%"
	       "lx"
	       "\n",
	       getFAR(), getESR());
	halt();
}
typedef struct readWordFromVSpace_ret {
	exception_t status;
	word_t value;
} readWordFromVSpace_ret_t;
static readWordFromVSpace_ret_t readWordFromVSpace(vspace_root_t *pd, word_t vaddr)
{
	lookupFrame_ret_t lookup_frame_ret;
	readWordFromVSpace_ret_t ret;
	word_t offset;
	pptr_t kernel_vaddr;
	word_t *value;
	lookup_frame_ret = lookupFrame(pd, vaddr);
	if (!lookup_frame_ret.valid) {
		ret.status = EXCEPTION_LOOKUP_FAULT;
		return ret;
	}
	offset = vaddr & ((1ul << (pageBitsForSize(lookup_frame_ret.frameSize))) - 1ul);
	kernel_vaddr = (word_t)ptrFromPAddr(lookup_frame_ret.frameBase);
	value = (word_t *)(kernel_vaddr + offset);
	ret.status = EXCEPTION_NONE;
	ret.value = *value;
	return ret;
}
void Arch_userStackTrace(tcb_t *tptr)
{
	cap_t threadRoot;
	vspace_root_t *vspaceRoot;
	word_t sp;
	threadRoot = (((cte_t *)((word_t)(tptr) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap;
	/* lookup the vspace root */
	if (cap_get_capType(threadRoot) != cap_page_global_directory_cap) {
		printf("Invalid vspace\n");
		return;
	}
	vspaceRoot = ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(threadRoot)));
	sp = getRegister(tptr, SP_EL0);
	/* check for alignment so we don't have to worry about accessing
	 * words that might be on two different pages */
	if (!(!((sp) & ((1ul << (3)) - 1ul)))) {
		printf("SP not aligned\n");
		return;
	}
	for (unsigned int i = 0; i < 16; i++) {
		word_t address = sp + (i * sizeof(word_t));
		readWordFromVSpace_ret_t result = readWordFromVSpace(vspaceRoot, address);
		if (result.status == EXCEPTION_NONE) {
			printf("0x%"
			       "lx"
			       ": 0x%"
			       "lx"
			       "\n",
			       address, result.value);
		} else {
			printf("0x%"
			       "lx"
			       ": INVALID\n",
			       address);
		}
	}
}
word_t get_tcb_sp(tcb_t *tcb)
{
	return tcb->tcbArch.tcbContext.registers[SP_EL0];
}
static void obj_frame_print_attrs(lookupFrame_ret_t ret);
static void cap_frame_print_attrs_pud(pude_t *pudSlot);
static void cap_frame_print_attrs_pd(pde_t *pdSlot);
static void cap_frame_print_attrs_pt(pte_t *ptSlot);
static void cap_frame_print_attrs_impl(word_t SH, word_t AP, word_t NXN);
static void cap_frame_print_attrs_vptr(word_t vptr, cap_t vspace);
static void _cap_frame_print_attrs_vptr(word_t vptr, vspace_root_t *vspaceRoot);
static void arm64_obj_pt_print_slots(pde_t *pdSlot);
static void arm64_obj_pd_print_slots(pude_t *pudSlot);
static void arm64_obj_pud_print_slots(void *pgdSlot_or_vspace);
static void arm64_cap_pt_print_slots(pde_t *pdSlot, vptr_t vptr);
static void arm64_cap_pd_print_slots(pude_t *pudSlot, vptr_t vptr);
static void arm64_cap_pud_print_slots(void *pgdSlot_or_vspace, vptr_t vptr);
/* Stage-1 access permissions:
 * AP[2:1]  higer EL        EL0
 *   00       rw            None
 *   01       rw            rw
 *   10       r             None
 *   11       r             r
 *
 * Stage-2 access permissions:
 * S2AP    Access from Nonsecure EL1 or Non-secure EL0
 *  00                      None
 *  01                      r
 *  10                      w
 *  11                      rw
 *
 *  For VMs or native seL4 applications, if hypervisor support
 *  is enabled, we use the S2AP. The kernel itself running in
 *  EL2 still uses the Stage-1 AP format.
 */
/* use when only have access to pte of frames */
static void cap_frame_print_attrs_pud(pude_t *pudSlot)
{
	cap_frame_print_attrs_impl(pude_pude_1g_ptr_get_SH(pudSlot),
				   pude_pude_1g_ptr_get_AP(pudSlot),
				   pude_pude_1g_ptr_get_UXN(pudSlot));
}
static void cap_frame_print_attrs_pd(pde_t *pdSlot)
{
	cap_frame_print_attrs_impl(pde_pde_large_ptr_get_SH(pdSlot),
				   pde_pde_large_ptr_get_AP(pdSlot),
				   pde_pde_large_ptr_get_UXN(pdSlot));
}
static void cap_frame_print_attrs_pt(pte_t *ptSlot)
{
	cap_frame_print_attrs_impl(pte_ptr_get_SH(ptSlot), pte_ptr_get_AP(ptSlot),
				   pte_ptr_get_UXN(ptSlot));
}
static void cap_frame_print_attrs_impl(word_t SH, word_t AP, word_t NXN)
{
	printf("(");
	/* rights */
	switch (AP) {
	case 0b00:
		break;
	case 0b01:
		printf("RW");
	case 0b10:
		break;
	case 0b11:
		printf("R");
	default:
		break;
	}
	if (!NXN) {
		printf("X");
	}
	/* Only has effect if SMP enabled */
	if (SH != 0) {
		printf(", uncached");
	}
	printf(")\n");
}
/* use when only have access to vptr of frames */
static void _cap_frame_print_attrs_vptr(word_t vptr, vspace_root_t *vspace)
{
	lookupPUDSlot_ret_t pudSlot = lookupPUDSlot(vspace, vptr);
	if (pudSlot.status != EXCEPTION_NONE) {
		return;
	}
	switch (pude_ptr_get_pude_type(pudSlot.pudSlot)) {
	case pude_pude_1g:
		printf("frame_%p_%04lu ", pudSlot.pudSlot,
		       (((vptr) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul)));
		cap_frame_print_attrs_pud(pudSlot.pudSlot);
		break;
	case pude_pude_pd: {
		pde_t *pd = ptrFromPAddr(pude_pude_pd_ptr_get_pd_base_address(pudSlot.pudSlot));
		pde_t *pdSlot = pd + (((vptr) >> (((12) + 9))) & ((1ul << (9)) - 1ul));
		switch (pde_ptr_get_pde_type(pdSlot)) {
		case pde_pde_large:
			printf("frame_%p_%04lu ", pdSlot,
			       (((vptr) >> (((12) + 9))) & ((1ul << (9)) - 1ul)));
			cap_frame_print_attrs_pd(pdSlot);
			break;
		case pde_pde_small: {
			pte_t *pt = ptrFromPAddr(pde_pde_small_ptr_get_pt_base_address(pdSlot));
			pte_t *ptSlot = pt + (((vptr) >> ((12))) & ((1ul << (9)) - 1ul));
			if (pte_ptr_get_present(ptSlot)) {
				printf("frame_%p_%04lu ", ptSlot,
				       (((vptr) >> ((12))) & ((1ul << (9)) - 1ul)));
				cap_frame_print_attrs_pt(ptSlot);
				break;
			} else {
				return;
			}
		}
		default:
			break;
		}
		break;
	}
	default:
		break;
	}
}
void cap_frame_print_attrs_vptr(word_t vptr, cap_t vspace)
{
	_cap_frame_print_attrs_vptr(vptr, ((vspace_root_t *)((pptr_t)cap_get_capPtr(vspace))));
}
/*
 * print object slots
 */
static void arm64_cap_pt_print_slots(pde_t *pdSlot, vptr_t vptr)
{
	pte_t *pt = ptrFromPAddr(pde_pde_small_ptr_get_pt_base_address(pdSlot));
	printf("pt_%p_%04lu {\n", pdSlot, (((vptr) >> (((12) + 9))) & ((1ul << (9)) - 1ul)));
	for (word_t i = 0; i < (1ul << ((12) + 9)); i += (1 << (12))) {
		pte_t *ptSlot = pt + (((i) >> ((12))) & ((1ul << (9)) - 1ul));
		if (pte_ptr_get_present(ptSlot)) {
			// print pte entries
			printf("0x%lx: frame_%p_%04lu", (((i) >> ((12))) & ((1ul << (9)) - 1ul)),
			       ptSlot, (((i) >> ((12))) & ((1ul << (9)) - 1ul)));
			cap_frame_print_attrs_pt(ptSlot);
		}
	}
	printf("}\n"); /* pt */
}
static void arm64_cap_pd_print_slots(pude_t *pudSlot, vptr_t vptr)
{
	printf("pd_%p_%04lu {\n", pudSlot, (((vptr) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul)));
	pde_t *pd = ptrFromPAddr(pude_pude_pd_ptr_get_pd_base_address(pudSlot));
	for (word_t i = 0; i < (1ul << (((12) + 9) + 9)); i += (1 << ((12) + 9))) {
		pde_t *pdSlot = pd + (((i) >> (((12) + 9))) & ((1ul << (9)) - 1ul));
		switch (pde_ptr_get_pde_type(pdSlot)) {
		case pde_pde_large:
			printf("0x%lx: frame_%p_%04lu",
			       (((i) >> (((12) + 9))) & ((1ul << (9)) - 1ul)), pdSlot,
			       (((i) >> (((12) + 9))) & ((1ul << (9)) - 1ul)));
			cap_frame_print_attrs_pd(pdSlot);
			break;
		case pde_pde_small:
			printf("0x%lx: pt_%p_%04lu\n",
			       (((i) >> (((12) + 9))) & ((1ul << (9)) - 1ul)), pdSlot,
			       (((i) >> (((12) + 9))) & ((1ul << (9)) - 1ul)));
			break;
		}
	}
	printf("}\n"); /* pd */
	for (word_t i = 0; i < (1ul << (((12) + 9) + 9)); i += (1 << ((12) + 9))) {
		pde_t *pdSlot = pd + (((i) >> (((12) + 9))) & ((1ul << (9)) - 1ul));
		if (pde_ptr_get_pde_type(pdSlot) == pde_pde_small) {
			arm64_cap_pt_print_slots(pdSlot, i);
		}
	}
}
static void arm64_cap_pud_print_slots(void *pgdSlot_or_vspace, vptr_t vptr)
{
	pude_t *pud = ptrFromPAddr(pgde_pgde_pud_ptr_get_pud_base_address(pgdSlot_or_vspace));
	printf("pud_%p_%04lu {\n", pgdSlot_or_vspace,
	       (((vptr) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul)));
	for (word_t i = 0; i < (1ul << ((((12) + 9) + 9) + 9)); i += (1 << (((12) + 9) + 9))) {
		pude_t *pudSlot = pud + (((i) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul));
		if (pude_ptr_get_pude_type(pudSlot) == pude_pude_pd) {
			printf("0x%lx: pd_%p_%04lu\n",
			       (((i) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul)), pudSlot,
			       (((i) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul)));
		}
	}
	printf("}\n"); /* pgd/pud */
	for (word_t i = 0; i < (1ul << ((((12) + 9) + 9) + 9)); i += (1 << (((12) + 9) + 9))) {
		pude_t *pudSlot = pud + (((i) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul));
		if (pude_ptr_get_pude_type(pudSlot) == pude_pude_pd) {
			arm64_cap_pd_print_slots(pudSlot, i);
		}
	}
}
void obj_vtable_print_slots(tcb_t *tcb)
{
	if (isVTableRoot(
		    (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap) &&
	    !seen((((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap)) {
		add_to_seen(
			(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap);
		vspace_root_t *vspace = ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(
			(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap)));
		/*
		 * ARM hyp uses 3 level translation rather than the usual 4 level.
		 * levels: PGD -> UPD -> PD -> PT
		 */
		printf("%p_pd {\n", vspace);
		for (word_t i = 0; i < (1ul << (((((12) + 9) + 9) + 9) + 9));
		     i += (1UL << ((((12) + 9) + 9) + 9))) {
			lookupPGDSlot_ret_t pgdSlot = lookupPGDSlot(vspace, i);
			if (pgde_pgde_pud_ptr_get_present(pgdSlot.pgdSlot)) {
				printf("0x%lx: pud_%p_%04lu\n",
				       (((i) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul)),
				       pgdSlot.pgdSlot,
				       (((i) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul)));
			}
		}
		printf("}\n"); /* pd */
		for (word_t i = 0; i < (1ul << (((((12) + 9) + 9) + 9) + 9));
		     i += (1UL << ((((12) + 9) + 9) + 9))) {
			lookupPGDSlot_ret_t pgdSlot = lookupPGDSlot(vspace, i);
			if (pgde_pgde_pud_ptr_get_present(pgdSlot.pgdSlot)) {
				arm64_cap_pud_print_slots(pgdSlot.pgdSlot, i);
			}
		}
	}
}
void print_ipc_buffer_slot(tcb_t *tcb)
{
	word_t vptr = tcb->tcbIPCBuffer;
	printf("ipc_buffer_slot: ");
	cap_frame_print_attrs_vptr(
		vptr, (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap);
}
void print_cap_arch(cap_t cap)
{
	switch (cap_get_capType(cap)) {
	case cap_page_table_cap: {
		asid_t asid = cap_page_table_cap_get_capPTMappedASID(cap);
		findVSpaceForASID_ret_t find_ret = findVSpaceForASID(asid);
		vptr_t vptr = cap_page_table_cap_get_capPTMappedAddress(cap);
		if (asid) {
			printf("pt_%p_%04lu (asid: %lu)\n",
			       lookupPDSlot(find_ret.vspace_root, vptr).pdSlot,
			       (((vptr) >> (((12) + 9))) & ((1ul << (9)) - 1ul)),
			       (long unsigned int)asid);
		} else {
			printf("pt_%p_%04lu\n", lookupPDSlot(find_ret.vspace_root, vptr).pdSlot,
			       (((vptr) >> (((12) + 9))) & ((1ul << (9)) - 1ul)));
		}
		break;
	}
	case cap_page_directory_cap: {
		asid_t asid = cap_page_directory_cap_get_capPDMappedASID(cap);
		findVSpaceForASID_ret_t find_ret = findVSpaceForASID(asid);
		vptr_t vptr = cap_page_directory_cap_get_capPDMappedAddress(cap);
		if (asid) {
			printf("pd_%p_%04lu (asid: %lu)\n",
			       lookupPUDSlot(find_ret.vspace_root, vptr).pudSlot,
			       (((vptr) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul)),
			       (long unsigned int)asid);
		} else {
			printf("pd_%p_%04lu\n", lookupPUDSlot(find_ret.vspace_root, vptr).pudSlot,
			       (((vptr) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul)));
		}
		break;
	}
	case cap_page_upper_directory_cap: {
		asid_t asid = cap_page_upper_directory_cap_get_capPUDMappedASID(cap);
		findVSpaceForASID_ret_t find_ret = findVSpaceForASID(asid);
		vptr_t vptr = cap_page_upper_directory_cap_get_capPUDMappedAddress(cap);
		if (asid) {
			printf("pud_%p_%04lu (asid: %lu)\n",
			       lookupPGDSlot(find_ret.vspace_root, vptr).pgdSlot,
			       (((vptr) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul)),
			       (long unsigned int)asid);
		} else {
			printf("pud_%p_%04lu\n", lookupPGDSlot(find_ret.vspace_root, vptr).pgdSlot,
			       (((vptr) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul)));
		}
		break;
	}
	case cap_page_global_directory_cap: {
		asid_t asid = cap_page_global_directory_cap_get_capPGDMappedASID(cap);
		findVSpaceForASID_ret_t find_ret = findVSpaceForASID(asid);
		if (asid) {
			printf("%p_pd (asid: %lu)\n", find_ret.vspace_root,
			       (long unsigned int)asid);
		} else {
			printf("%p_pd\n", find_ret.vspace_root);
		}
		break;
	}
	case cap_asid_control_cap: {
		/* only one in the system */
		printf("asid_control\n");
		break;
	}
	case cap_frame_cap: {
		vptr_t vptr = cap_frame_cap_get_capFMappedAddress(cap);
		findVSpaceForASID_ret_t find_ret =
			findVSpaceForASID(cap_frame_cap_get_capFMappedASID(cap));
		_cap_frame_print_attrs_vptr(vptr, find_ret.vspace_root);
		break;
	}
	case cap_asid_pool_cap: {
		printf("%p_asid_pool\n", (void *)cap_asid_pool_cap_get_capASIDPool(cap));
		break;
	}
		/* ARM specific caps */
	default: {
		printf("[unknown cap %lu]\n", (long unsigned int)cap_get_capType(cap));
		break;
	}
	}
}
void print_object_arch(cap_t cap)
{
	switch (cap_get_capType(cap)) {
	case cap_frame_cap:
	case cap_page_table_cap:
	case cap_page_directory_cap:
	case cap_page_upper_directory_cap:
	case cap_page_global_directory_cap:
		/* don't need to deal with these objects since they get handled from vtable */
		break;
	case cap_asid_pool_cap: {
		printf("%p_asid_pool = asid_pool ", (void *)cap_asid_pool_cap_get_capASIDPool(cap));
		obj_asidpool_print_attrs(cap);
		break;
	}
		/* ARM specific objects */
	default: {
		printf("[unknown object %lu]\n", (long unsigned int)cap_get_capType(cap));
		break;
	}
	}
}
void obj_frame_print_attrs(lookupFrame_ret_t ret)
{
	printf("(");
	/* VM size */
	switch (ret.frameSize) {
	case ARMHugePage:
		printf("1G");
		break;
	case ARMLargePage:
		printf("2M");
		break;
	case ARMSmallPage:
		printf("4k");
		break;
	}
	printf(", paddr: 0x%p)\n", (void *)ret.frameBase);
}
void arm64_obj_pt_print_slots(pde_t *pdSlot)
{
	lookupFrame_ret_t ret;
	pte_t *pt = ptrFromPAddr(pde_pde_small_ptr_get_pt_base_address(pdSlot));
	for (word_t i = 0; i < (1ul << ((12) + 9)); i += (1 << (12))) {
		pte_t *ptSlot = pt + (((i) >> ((12))) & ((1ul << (9)) - 1ul));
		if (pte_ptr_get_present(ptSlot)) {
			ret.frameBase = pte_ptr_get_page_base_address(ptSlot);
			ret.frameSize = ARMSmallPage;
			printf("frame_%p_%04lu = frame ", ptSlot,
			       (((i) >> ((12))) & ((1ul << (9)) - 1ul)));
			obj_frame_print_attrs(ret);
		}
	}
}
void arm64_obj_pd_print_slots(pude_t *pudSlot)
{
	lookupFrame_ret_t ret;
	pde_t *pd = ptrFromPAddr(pude_pude_pd_ptr_get_pd_base_address(pudSlot));
	for (word_t i = 0; i < (1ul << (((12) + 9) + 9)); i += (1 << ((12) + 9))) {
		pde_t *pdSlot = pd + (((i) >> (((12) + 9))) & ((1ul << (9)) - 1ul));
		if (pde_ptr_get_pde_type(pdSlot) == pde_pde_large) {
			ret.frameBase = pde_pde_large_ptr_get_page_base_address(pdSlot);
			ret.frameSize = ARMLargePage;
			printf("frame_%p_%04lu = frame ", pdSlot,
			       (((i) >> (((12) + 9))) & ((1ul << (9)) - 1ul)));
			obj_frame_print_attrs(ret);
		}
		if (pde_ptr_get_pde_type(pdSlot) == pde_pde_small) {
			printf("pt_%p_%04lu = pt\n", pdSlot,
			       (((i) >> (((12) + 9))) & ((1ul << (9)) - 1ul)));
			arm64_obj_pt_print_slots(pdSlot);
		}
	}
}
void arm64_obj_pud_print_slots(void *pgdSlot_or_vspace)
{
	lookupFrame_ret_t ret;
	pude_t *pud = ptrFromPAddr(pgde_pgde_pud_ptr_get_pud_base_address(pgdSlot_or_vspace));
	for (word_t i = 0; i < (1ul << ((((12) + 9) + 9) + 9)); i += (1 << (((12) + 9) + 9))) {
		pude_t *pudSlot = pud + (((i) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul));
		switch (pude_ptr_get_pude_type(pudSlot)) {
		case pude_pude_1g:
			ret.frameBase = pude_pude_1g_ptr_get_page_base_address(pudSlot);
			ret.frameSize = ARMHugePage;
			printf("frame_%p_%04lu = frame ", pudSlot,
			       (((i) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul)));
			obj_frame_print_attrs(ret);
			break;
		case pude_pude_pd: {
			printf("pd_%p_%04lu = pd\n", pudSlot,
			       (((i) >> ((((12) + 9) + 9))) & ((1ul << (9)) - 1ul)));
			arm64_obj_pd_print_slots(pudSlot);
		}
		}
	}
}
void obj_tcb_print_vtable(tcb_t *tcb)
{
	if (isVTableRoot(
		    (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap) &&
	    !seen((((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap)) {
		add_to_seen(
			(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap);
		vspace_root_t *vspace = ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(
			(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap)));
		/*
		 * ARM hyp uses 3 level translation rather than the usual 4 level.
		 * levels: PGD -> PUD -> PD -> PT
		 */
		printf("%p_pd = pgd\n", vspace);
		for (word_t i = 0; i < (1ul << (((((12) + 9) + 9) + 9) + 9));
		     i += (1UL << ((((12) + 9) + 9) + 9))) {
			lookupPGDSlot_ret_t pgdSlot = lookupPGDSlot(vspace, i);
			if (pgde_pgde_pud_ptr_get_present(pgdSlot.pgdSlot)) {
				printf("pud_%p_%04lu = pud\n", pgdSlot.pgdSlot,
				       (((i) >> (((((12) + 9) + 9) + 9))) & ((1ul << (9)) - 1ul)));
				arm64_obj_pud_print_slots(pgdSlot.pgdSlot);
			}
		}
	}
}
void debug_capDL(void)
{
	printf("arch aarch64\n");
	printf("objects {\n");
	print_objects();
	printf("}\n");
	printf("caps {\n");
	/* reset the seen list */
	reset_seen_list();
	print_caps();
	printf("}\n");
	obj_irq_print_maps();
}
bool_t isFPUEnabledCached[1];
/* Initialise the FP/SIMD for this machine. */
bool_t fpsimd_init(void)
{
	/* Set the FPU to lazy switch mode */
	disableFpu();
	return true;
}
bool_t fpsimd_HWCapTest(void)
{
	word_t id_aa64pfr0;
	/* Check if the hardware has FP and ASIMD support... */
	__asm__ volatile("mrs %x0,"
			 "id_aa64pfr0_el1"
			 : "=r"(id_aa64pfr0));
	if (((id_aa64pfr0 >> 16 /* HWCap for Floating Point*/) & ((1ul << (4)) - 1ul)) ==
		    ((1ul << (4)) - 1ul) ||
	    ((id_aa64pfr0 >> 20 /* HWCap for Advanced SIMD*/) & ((1ul << (4)) - 1ul)) ==
		    ((1ul << (4)) - 1ul)) {
		return false;
	}
	return true;
}
const register_t msgRegisters[] = {X2, X3, X4, X5};
_Static_assert(sizeof(msgRegisters) / sizeof(msgRegisters[0]) == n_msgRegisters,
	       "consistent_message_registers");
;
const register_t frameRegisters[] = {FaultIP, SP_EL0, SPSR_EL1, X0,  X1,  X2,  X3,  X4, X5,
				     X6,      X7,     X8,	X16, X17, X18, X29, X30};
_Static_assert(sizeof(frameRegisters) / sizeof(frameRegisters[0]) == n_frameRegisters,
	       "consistent_frame_registers");
;
const register_t gpRegisters[] = {
	X9,  X10, X11, X12, X13, X14, X15, X19,	      X20,	   X21,
	X22, X23, X24, X25, X26, X27, X28, TPIDR_EL0, TPIDRRO_EL0,
};
_Static_assert(sizeof(gpRegisters) / sizeof(gpRegisters[0]) == n_gpRegisters,
	       "consistent_gp_registers");
;
asid_pool_t *armKSASIDTable[(1ul << (asidHighBits))];
/* AArch64 Memory map explanation:
 *
 * EL1 and EL2 kernel build vaddrspace layouts:
 *
 * On AArch64, the EL1 and EL2 builds of the kernel both use approx 512GiB of
 * virtual address space.
 *
 * The EL1 kernel resides within approx 512 GiB of virtual memory somewhere
 * within the canonical top (not necessarily the same as the actual top, but all
 * the unused high bits of kernel virtual addresses are set to 1) of every
 * user VSpace.
 *
 * The EL2 kernel resides within approx 512 GiB of virtual memory somewhere
 * within the canonical bottom (all the unused high bits are set to 0) of its
 * own separate virtual address space.
 *
 * Common Aarch64 address space layout:
 *
 * The reason why 512 GiB was chosen is because assuming a 48-bit virtual
 * address space using a 4KiB Translation Granule (and therefore, 4 levels of
 * page tables):
 *
 * One top-level page-structure entry maps 512 GiB, so by limiting ourselves to
 * 512 GiB, we only need to pre-allocate 1 level0 table (lvl0 is the top level),
 * 1 level1 table, 512 level2 tables (with each level2 entry mapping 2MiB), and
 * skip level3.
 *
 * We do maintain a single level3 table however, which is mapped into the last
 * entry in the last level2 table, such that the last 2MiB are mapped using
 * 4KiB pages instead of 2MiB pages. The reason for this last 2MiB being mapped
 * using small pages is because this last 2MiB is where the kernel maps all the
 * different devices it uses (see map_kernel_devices()). This implies that the
 * kernel can only have up to approx 512GiB of kernel untypeds.
 *
 * If you wish for your AArch64 platform to use more than 512 GiB of virtual
 * memory, you will need to change the number of pre-allocated page tables below
 * to be sufficient to contain the mapping you want. And don't forget to update
 * this comment here afterward.
 */
/* User vaddrspace layouts:
 *
 * For EL2:
 *
 * A plain-english explanation of the memory layout is that the
 * the user address spaces cover the address range from 0x0 to the maximum
 * IPA.
 *
 * So for a CPU that can generate 44 bits of IPA/PA (such as the TX1/TX2), user
 * vaddr spaces will cover 16TiB from 0x0 to 0x00000fff_ffffffff.
 *
 * Basically by making the guest physical address spaces 44 bits, the guest
 * kernels can access all of (what they think is) physical memory, while
 * allowing us to potentially trap accesses by the guests to physical memory
 * beyond what the processor can address.
 *
 * For EL1:
 *
 * The standard canonical-high and canonical-low split using TCR_EL1.TBI
 * applies.
 */
vspace_root_t armKSGlobalUserVSpace[(1ul << (9))] __attribute__((__aligned__((1ul << (12)))));
pgde_t armKSGlobalKernelPGD[(1ul << (9))] __attribute__((__aligned__((1ul << (12)))));
pude_t armKSGlobalKernelPUD[(1ul << (9))] __attribute__((__aligned__((1ul << (12)))));
pde_t armKSGlobalKernelPDs[(1ul << (9))][(1ul << (9))] __attribute__((__aligned__((1ul << (12)))));
pte_t armKSGlobalKernelPT[(1ul << (9))] __attribute__((__aligned__((1ul << (12)))));
bool_t Arch_isFrameType(word_t type)
{
	switch (type) {
	case seL4_ARM_SmallPageObject:
		return true;
	case seL4_ARM_LargePageObject:
		return true;
	case seL4_ARM_HugePageObject:
		return true;
	default:
		return false;
	}
}
deriveCap_ret_t Arch_deriveCap(cte_t *slot, cap_t cap)
{
	deriveCap_ret_t ret;
	switch (cap_get_capType(cap)) {
	case cap_page_global_directory_cap:
		if (cap_page_global_directory_cap_get_capPGDIsMapped(cap)) {
			ret.cap = cap;
			ret.status = EXCEPTION_NONE;
		} else {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Deriving a PDG "
				       "cap without an assigned ASID>>\n",
				       0lu, __func__, 40, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_IllegalOperation;
			ret.cap = cap_null_cap_new();
			ret.status = EXCEPTION_SYSCALL_ERROR;
		}
		return ret;
	case cap_page_upper_directory_cap:
		if (cap_page_upper_directory_cap_get_capPUDIsMapped(cap)) {
			ret.cap = cap;
			ret.status = EXCEPTION_NONE;
		} else {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Deriving a PUD "
				       "cap without an assigned ASID>>\n",
				       0lu, __func__, 52, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_IllegalOperation;
			ret.cap = cap_null_cap_new();
			ret.status = EXCEPTION_SYSCALL_ERROR;
		}
		return ret;
	case cap_page_directory_cap:
		if (cap_page_directory_cap_get_capPDIsMapped(cap)) {
			ret.cap = cap;
			ret.status = EXCEPTION_NONE;
		} else {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Deriving a PD cap "
				       "without an assigned ASID>>\n",
				       0lu, __func__, 64, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_IllegalOperation;
			ret.cap = cap_null_cap_new();
			ret.status = EXCEPTION_SYSCALL_ERROR;
		}
		return ret;
	case cap_page_table_cap:
		if (cap_page_table_cap_get_capPTIsMapped(cap)) {
			ret.cap = cap;
			ret.status = EXCEPTION_NONE;
		} else {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Deriving a PT cap "
				       "without an assigned ASID>>\n",
				       0lu, __func__, 76, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_IllegalOperation;
			ret.cap = cap_null_cap_new();
			ret.status = EXCEPTION_SYSCALL_ERROR;
		}
		return ret;
	case cap_frame_cap:
		ret.cap = cap_frame_cap_set_capFMappedASID(cap, asidInvalid);
		ret.status = EXCEPTION_NONE;
		return ret;
	case cap_asid_control_cap:
	case cap_asid_pool_cap:
		ret.cap = cap;
		ret.status = EXCEPTION_NONE;
		return ret;
	default:
		/* This assert has no equivalent in haskell,
		 * as the options are restricted by type */
		_fail("Invalid arch cap",
		      "/home/lab/projects/seL4/seL4test/kernel/src/arch/arm/64/object/objecttype.c",
		      115, __func__);
	}
}
cap_t Arch_updateCapData(bool_t preserve, word_t data, cap_t cap)
{
	return cap;
}
cap_t Arch_maskCapRights(seL4_CapRights_t cap_rights_mask, cap_t cap)
{
	if (cap_get_capType(cap) == cap_frame_cap) {
		vm_rights_t vm_rights;
		vm_rights = vmRightsFromWord(cap_frame_cap_get_capFVMRights(cap));
		vm_rights = maskVMRights(vm_rights, cap_rights_mask);
		return cap_frame_cap_set_capFVMRights(cap, wordFromVMRights(vm_rights));
	} else {
		return cap;
	}
}
finaliseCap_ret_t Arch_finaliseCap(cap_t cap, bool_t final)
{
	finaliseCap_ret_t fc_ret;
	switch (cap_get_capType(cap)) {
	case cap_asid_pool_cap:
		if (final) {
			deleteASIDPool(cap_asid_pool_cap_get_capASIDBase(cap),
				       ((asid_pool_t *)cap_asid_pool_cap_get_capASIDPool(cap)));
		}
		break;
	case cap_page_global_directory_cap:
		if (final && cap_page_global_directory_cap_get_capPGDIsMapped(cap)) {
			deleteASID(
				cap_page_global_directory_cap_get_capPGDMappedASID(cap),
				((vspace_root_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(
					cap))));
		}
		break;
	case cap_page_upper_directory_cap:
		if (final && cap_page_upper_directory_cap_get_capPUDIsMapped(cap)) {
			unmapPageUpperDirectory(
				cap_page_upper_directory_cap_get_capPUDMappedASID(cap),
				cap_page_upper_directory_cap_get_capPUDMappedAddress(cap),
				((pude_t *)(cap_page_upper_directory_cap_get_capPUDBasePtr(cap))));
		}
		break;
	case cap_page_directory_cap:
		if (final && cap_page_directory_cap_get_capPDIsMapped(cap)) {
			unmapPageDirectory(
				cap_page_directory_cap_get_capPDMappedASID(cap),
				cap_page_directory_cap_get_capPDMappedAddress(cap),
				((pde_t *)(cap_page_directory_cap_get_capPDBasePtr(cap))));
		}
		break;
	case cap_page_table_cap:
		if (final && cap_page_table_cap_get_capPTIsMapped(cap)) {
			unmapPageTable(cap_page_table_cap_get_capPTMappedASID(cap),
				       cap_page_table_cap_get_capPTMappedAddress(cap),
				       ((pte_t *)(cap_page_table_cap_get_capPTBasePtr(cap))));
		}
		break;
	case cap_frame_cap:
		if (cap_frame_cap_get_capFMappedASID(cap)) {
			unmapPage(cap_frame_cap_get_capFSize(cap),
				  cap_frame_cap_get_capFMappedASID(cap),
				  cap_frame_cap_get_capFMappedAddress(cap),
				  cap_frame_cap_get_capFBasePtr(cap));
		}
		break;
	}
	fc_ret.remainder = cap_null_cap_new();
	fc_ret.cleanupInfo = cap_null_cap_new();
	return fc_ret;
}
bool_t Arch_sameRegionAs(cap_t cap_a, cap_t cap_b)
{
	switch (cap_get_capType(cap_a)) {
	case cap_frame_cap:
		if (cap_get_capType(cap_b) == cap_frame_cap) {
			word_t botA, botB, topA, topB;
			botA = cap_frame_cap_get_capFBasePtr(cap_a);
			botB = cap_frame_cap_get_capFBasePtr(cap_b);
			topA = botA +
			       ((1ul << (pageBitsForSize(cap_frame_cap_get_capFSize(cap_a)))) -
				1ul);
			topB = botB +
			       ((1ul << (pageBitsForSize(cap_frame_cap_get_capFSize(cap_b)))) -
				1ul);
			return ((botA <= botB) && (topA >= topB) && (botB <= topB));
		}
		break;
	case cap_page_table_cap:
		if (cap_get_capType(cap_b) == cap_page_table_cap) {
			return cap_page_table_cap_get_capPTBasePtr(cap_a) ==
			       cap_page_table_cap_get_capPTBasePtr(cap_b);
		}
		break;
	case cap_page_directory_cap:
		if (cap_get_capType(cap_b) == cap_page_directory_cap) {
			return cap_page_directory_cap_get_capPDBasePtr(cap_a) ==
			       cap_page_directory_cap_get_capPDBasePtr(cap_b);
		}
		break;
	case cap_page_upper_directory_cap:
		if (cap_get_capType(cap_b) == cap_page_upper_directory_cap) {
			return cap_page_upper_directory_cap_get_capPUDBasePtr(cap_a) ==
			       cap_page_upper_directory_cap_get_capPUDBasePtr(cap_b);
		}
		break;
	case cap_page_global_directory_cap:
		if (cap_get_capType(cap_b) == cap_page_global_directory_cap) {
			return cap_page_global_directory_cap_get_capPGDBasePtr(cap_a) ==
			       cap_page_global_directory_cap_get_capPGDBasePtr(cap_b);
		}
		break;
	case cap_asid_control_cap:
		if (cap_get_capType(cap_b) == cap_asid_control_cap) {
			return true;
		}
		break;
	case cap_asid_pool_cap:
		if (cap_get_capType(cap_b) == cap_asid_pool_cap) {
			return cap_asid_pool_cap_get_capASIDPool(cap_a) ==
			       cap_asid_pool_cap_get_capASIDPool(cap_b);
		}
		break;
	}
	return false;
}
bool_t Arch_sameObjectAs(cap_t cap_a, cap_t cap_b)
{
	if (cap_get_capType(cap_a) == cap_frame_cap) {
		if (cap_get_capType(cap_b) == cap_frame_cap) {
			return ((cap_frame_cap_get_capFBasePtr(cap_a) ==
				 cap_frame_cap_get_capFBasePtr(cap_b)) &&
				(cap_frame_cap_get_capFSize(cap_a) ==
				 cap_frame_cap_get_capFSize(cap_b)) &&
				((cap_frame_cap_get_capFIsDevice(cap_a) == 0) ==
				 (cap_frame_cap_get_capFIsDevice(cap_b) == 0)));
		}
	}
	return Arch_sameRegionAs(cap_a, cap_b);
}
word_t Arch_getObjectSize(word_t t)
{
	switch (t) {
	case seL4_ARM_SmallPageObject:
		return ARMSmallPageBits;
	case seL4_ARM_LargePageObject:
		return ARMLargePageBits;
	case seL4_ARM_HugePageObject:
		return ARMHugePageBits;
	case seL4_ARM_PageTableObject:
		return 12;
	case seL4_ARM_PageDirectoryObject:
		return 12;
	case seL4_ARM_PageUpperDirectoryObject:
		return 12;
	case seL4_ARM_PageGlobalDirectoryObject:
		return 12;
	default:
		_fail("Invalid object type",
		      "/home/lab/projects/seL4/seL4test/kernel/src/arch/arm/64/object/objecttype.c",
		      381, __func__);
		return 0;
	}
}
cap_t Arch_createObject(object_t t, void *regionBase, word_t userSize, bool_t deviceMemory)
{
	switch (t) {
	case seL4_ARM_SmallPageObject:
		return cap_frame_cap_new(asidInvalid,	     /* capFMappedASID */
					 (word_t)regionBase, /* capFBasePtr */
					 ARMSmallPage,	     /* capFSize */
					 0,		     /* capFMappedAddress */
					 VMReadWrite,	     /* capFVMRights */
					 !!deviceMemory	     /* capFIsDevice */
		);
	case seL4_ARM_LargePageObject:
		return cap_frame_cap_new(asidInvalid,	     /* capFMappedASID */
					 (word_t)regionBase, /* capFBasePtr */
					 ARMLargePage,	     /* capFSize */
					 0,		     /* capFMappedAddress */
					 VMReadWrite,	     /* capFVMRights */
					 !!deviceMemory	     /* capFIsDevice */
		);
	case seL4_ARM_HugePageObject:
		return cap_frame_cap_new(asidInvalid,	     /* capFMappedASID */
					 (word_t)regionBase, /* capFBasePtr */
					 ARMHugePage,	     /* capFSize */
					 0,		     /* capFMappedAddress */
					 VMReadWrite,	     /* capFVMRights */
					 !!deviceMemory	     /* capFIsDevice */
		);
	case seL4_ARM_PageGlobalDirectoryObject:
		return cap_page_global_directory_cap_new(asidInvalid, /* capPGDMappedASID   */
							 (word_t)regionBase, /* capPGDBasePtr */
							 0 /* capPGDIsMapped     */
		);
	case seL4_ARM_PageUpperDirectoryObject:
		return cap_page_upper_directory_cap_new(asidInvalid, /* capPUDMappedASID    */
							(word_t)regionBase, /* capPUDBasePtr */
							0, /* capPUDIsMapped      */
							0  /* capPUDMappedAddress */
		);
	case seL4_ARM_PageDirectoryObject:
		return cap_page_directory_cap_new(asidInvalid,	      /* capPDMappedASID    */
						  (word_t)regionBase, /* capPDBasePtr       */
						  0,		      /* capPDIsMapped      */
						  0		      /* capPDMappedAddress */
		);
	case seL4_ARM_PageTableObject:
		return cap_page_table_cap_new(asidInvalid,	  /* capPTMappedASID    */
					      (word_t)regionBase, /* capPTBasePtr       */
					      0,		  /* capPTIsMapped      */
					      0			  /* capPTMappedAddress */
		);
	default:
		_fail("Arch_createObject got an API type or invalid object type",
		      "/home/lab/projects/seL4/seL4test/kernel/src/arch/arm/64/object/objecttype.c",
		      470, __func__);
	}
}
exception_t Arch_decodeInvocation(word_t label, word_t length, cptr_t cptr, cte_t *slot, cap_t cap,
				  bool_t call, word_t *buffer)
{
	return decodeARMMMUInvocation(label, length, cptr, slot, cap, buffer);
}
void Arch_prepareThreadDelete(tcb_t *thread)
{
	fpuThreadDelete(thread);
}
bool_t Arch_handleFaultReply(tcb_t *receiver, tcb_t *sender, word_t faultType)
{
	switch (faultType) {
	case seL4_Fault_VMFault:
		return true;
	default:
		_fail("Invalid fault",
		      "/home/lab/projects/seL4/seL4test/kernel/src/arch/arm/api/faults.c", 29,
		      __func__);
	}
}
word_t Arch_setMRs_fault(tcb_t *sender, tcb_t *receiver, word_t *receiveIPCBuffer, word_t faultType)
{
	switch (faultType) {
	case seL4_Fault_VMFault: {
		setMR(receiver, receiveIPCBuffer, seL4_VMFault_IP, getRestartPC(sender));
		setMR(receiver, receiveIPCBuffer, seL4_VMFault_Addr,
		      seL4_Fault_VMFault_get_address(sender->tcbFault));
		setMR(receiver, receiveIPCBuffer, seL4_VMFault_PrefetchFault,
		      seL4_Fault_VMFault_get_instructionFault(sender->tcbFault));
		return setMR(receiver, receiveIPCBuffer, seL4_VMFault_FSR,
			     seL4_Fault_VMFault_get_FSR(sender->tcbFault));
	}
	default:
		_fail("Invalid fault",
		      "/home/lab/projects/seL4/seL4test/kernel/src/arch/arm/api/faults.c", 68,
		      __func__);
	}
}
static inline void cleanByWSL(word_t wsl)
{
	__asm__ volatile("dc csw, %0" : : "r"(wsl));
}
static inline void cleanInvalidateByWSL(word_t wsl)
{
	__asm__ volatile("dc cisw, %0" : : "r"(wsl));
}
static inline word_t readCLID(void)
{
	word_t CLID;
	__asm__ volatile("mrs %x0,"
			 "clidr_el1"
			 : "=r"(CLID));
	return CLID;
}
enum arm_cache_type {
	ARMCacheI = 1,
	ARMCacheD = 2,
	ARMCacheID = 3,
};
static inline word_t readCacheSize(int level, bool_t instruction)
{
	word_t size, csselr_old;
	/* Save CSSELR */
	__asm__ volatile("mrs %x0,"
			 "csselr_el1"
			 : "=r"(csselr_old));
	/* Select cache level */
	do {
		word_t _v = ((level << 1) | instruction);
		__asm__ volatile("msr "
				 "csselr_el1"
				 ",%x0" ::"r"(_v));
	} while (0);
	/* Read 'size' */
	__asm__ volatile("mrs %x0,"
			 "ccsidr_el1"
			 : "=r"(size));
	/* Restore CSSELR */
	do {
		word_t _v = csselr_old;
		__asm__ volatile("msr "
				 "csselr_el1"
				 ",%x0" ::"r"(_v));
	} while (0);
	return size;
}
void clean_D_PoU(void)
{
	int clid = readCLID();
	int lou = (((clid) >> 27) & ((1ul << (3)) - 1ul));
	for (int l = 0; l < lou; l++) {
		if ((((clid) >> (l * 3)) & ((1ul << (3)) - 1ul)) > ARMCacheI) {
			word_t lsize = readCacheSize(l, 0);
			int lbits = (((lsize) & ((1ul << (3)) - 1ul)) + 4);
			int assoc = ((((lsize) >> 3) & ((1ul << (10)) - 1ul)) + 1);
			int assoc_bits = (1 << 6) - clzl(assoc - 1);
			int nsets = ((((lsize) >> 13) & ((1ul << (15)) - 1ul)) + 1);
			for (int w = 0; w < assoc; w++) {
				for (int s = 0; s < nsets; s++) {
					cleanByWSL((w << (32 - assoc_bits)) | (s << lbits) |
						   (l << 1));
				}
			}
		}
	}
}
static inline void cleanInvalidate_D_by_level(int l)
{
	word_t lsize = readCacheSize(l, 0);
	int lbits = (((lsize) & ((1ul << (3)) - 1ul)) + 4);
	int assoc = ((((lsize) >> 3) & ((1ul << (10)) - 1ul)) + 1);
	int assoc_bits = (1 << 6) - clzl(assoc - 1);
	int nsets = ((((lsize) >> 13) & ((1ul << (15)) - 1ul)) + 1);
	for (int w = 0; w < assoc; w++) {
		for (int s = 0; s < nsets; s++) {
			cleanInvalidateByWSL((w << (32 - assoc_bits)) | (s << lbits) | (l << 1));
		}
	}
}
void cleanInvalidate_D_PoC(void)
{
	int clid = readCLID();
	int loc = (((clid) >> 24) & ((1ul << (3)) - 1ul));
	for (int l = 0; l < loc; l++) {
		if ((((clid) >> (l * 3)) & ((1ul << (3)) - 1ul)) > ARMCacheI) {
			cleanInvalidate_D_by_level(l);
		}
	}
}
void cleanInvalidate_L1D(void)
{
	cleanInvalidate_D_by_level(0);
}
void armv_init_user_access(void);
/* bits in the CNTKCTL_EL1 */
/* bits in CNTHCTL_EL2 */
static void check_export_pmu(void) {}
static void check_export_arch_timer(void)
{
	uint32_t val = 0;
	do {
		word_t _v = val;
		__asm__ volatile("msr "
				 "CNTKCTL_EL1"
				 ",%x0" ::"r"(_v));
	} while (0);
}
void armv_init_user_access(void)
{
	check_export_pmu();
	check_export_arch_timer();
}
void c_handle_undefined_instruction(void)
{
	c_entry_hook();
	ksKernelEntry.path = Entry_UserLevelFault;
	ksKernelEntry.word = getRegister(ksCurThread, NextIP);
	/* There's only one user-level fault on ARM, and the code is (0,0) */
	handleUserLevelFault(getESR(), 0);
	restore_user_context();
	__builtin_unreachable();
}
void c_handle_enfp(void)
{
	c_entry_hook();
	handleFPUFault();
	restore_user_context();
	__builtin_unreachable();
}
static inline void c_handle_vm_fault(vm_fault_type_t type)
{
	c_entry_hook();
	ksKernelEntry.path = Entry_VMFault;
	ksKernelEntry.word = getRegister(ksCurThread, NextIP);
	handleVMFaultEvent(type);
	restore_user_context();
	__builtin_unreachable();
}
void c_handle_data_fault(void)
{
	c_handle_vm_fault(0);
}
void c_handle_instruction_fault(void)
{
	c_handle_vm_fault(1);
}
void c_handle_interrupt(void)
{
	c_entry_hook();
	ksKernelEntry.path = Entry_Interrupt;
	ksKernelEntry.word = (getActiveIRQ());
	ksKernelEntry.core = 0lu;
	handleInterruptEntry();
	restore_user_context();
}
void slowpath(syscall_t syscall)
{
	if (__builtin_expect(!!(syscall < (-8) || syscall > (-1)), 0)) {
		ksKernelEntry.path = Entry_UnknownSyscall;
		/* ksKernelEntry.word word is already set to syscall */
		/* Contrary to the name, this handles all non-standard syscalls used in
		 * debug builds also.
		 */
		handleUnknownSyscall(syscall);
	} else {
		ksKernelEntry.is_fastpath = 0;
		handleSyscall(syscall);
	}
	restore_user_context();
	__builtin_unreachable();
}
void c_handle_syscall(word_t cptr, word_t msgInfo, syscall_t syscall)
{
	c_entry_hook();
	benchmark_debug_syscall_start(cptr, msgInfo, syscall);
	ksKernelEntry.is_fastpath = 0;
	slowpath(syscall);
	__builtin_unreachable();
}
void c_handle_fastpath_call(word_t cptr, word_t msgInfo)
{
	c_entry_hook();
	benchmark_debug_syscall_start(cptr, msgInfo, SysCall);
	ksKernelEntry.is_fastpath = 1;
	fastpath_call(cptr, msgInfo);
	__builtin_unreachable();
}
void c_handle_fastpath_reply_recv(word_t cptr, word_t msgInfo)
{
	c_entry_hook();
	benchmark_debug_syscall_start(cptr, msgInfo, SysReplyRecv);
	ksKernelEntry.is_fastpath = 1;
	fastpath_reply_recv(cptr, msgInfo);
	__builtin_unreachable();
}
cap_t create_unmapped_it_frame_cap(pptr_t pptr, bool_t use_large);
cap_t create_mapped_it_frame_cap(cap_t pd_cap, pptr_t pptr, vptr_t vptr, asid_t asid,
				 bool_t use_large, bool_t executable);
void init_kernel(paddr_t ui_p_reg_start, paddr_t ui_p_reg_end, sword_t pv_offset, vptr_t v_entry,
		 paddr_t dtb_addr_p, uint32_t dtb_size);
static region_t reserved[(3 + 0)];
static bool_t arch_init_freemem(p_region_t ui_p_reg, p_region_t dtb_p_reg, v_region_t it_v_reg,
				word_t extra_bi_size_bits)
{
	/* reserve the kernel image region */
	reserved[0].start = KERNEL_ELF_BASE;
	reserved[0].end = (pptr_t)ki_end;
	int index = 1;
	/* add the dtb region, if it is not empty */
	if (dtb_p_reg.start) {
		if (index >= (sizeof(reserved) / sizeof((reserved)[0]))) {
			printf("ERROR: no slot to add DTB to reserved regions\n");
			return false;
		}
		reserved[index].start = (pptr_t)ptrFromPAddr(dtb_p_reg.start);
		reserved[index].end = (pptr_t)ptrFromPAddr(dtb_p_reg.end);
		index++;
	}
	/* Reserve the user image region and the mode-reserved regions. For now,
	 * only one mode-reserved region is supported, because this is all that is
	 * needed.
	 */
	if (0 > 1) {
		printf("ERROR: MODE_RESERVED > 1 unsupported!\n");
		return false;
	}
	if (ui_p_reg.start < (PPTR_TOP - (PPTR_BASE - 0x0ul))) {
		region_t ui_reg = paddr_to_pptr_reg(ui_p_reg);
		if (0 == 1) {
			if (index + 1 >= (sizeof(reserved) / sizeof((reserved)[0]))) {
				printf("ERROR: no slot to add the user image and the "
				       "mode-reserved region to the reserved regions\n");
				return false;
			}
			if (ui_reg.end > mode_reserved_region[0].start) {
				reserved[index] = mode_reserved_region[0];
				index++;
				reserved[index] = ui_reg;
			} else {
				reserved[index] = ui_reg;
				index++;
				reserved[index] = mode_reserved_region[0];
			}
			index++;
		} else {
			if (index >= (sizeof(reserved) / sizeof((reserved)[0]))) {
				printf("ERROR: no slot to add the user image to the reserved"
				       "regions\n");
				return false;
			}
			reserved[index] = ui_reg;
			index++;
		}
	} else {
		if (0 == 1) {
			if (index >= (sizeof(reserved) / sizeof((reserved)[0]))) {
				printf("ERROR: no slot to add the mode-reserved region\n");
				return false;
			}
			reserved[index] = mode_reserved_region[0];
			index++;
		}
		/* Reserve the ui_p_reg region still so it doesn't get turned into device UT. */
		reserve_region(ui_p_reg);
	}
	/* avail_p_regs comes from the auto-generated code */
	return init_freemem((sizeof(avail_p_regs) / sizeof((avail_p_regs)[0])), avail_p_regs, index,
			    reserved, it_v_reg, extra_bi_size_bits);
}
static void init_irqs(cap_t root_cnode_cap)
{
	unsigned i;
	for (i = 0; i <= maxIRQ; i++) {
		setIRQState(IRQInactive, (i));
	}
	setIRQState(IRQTimer, (27));
	/* provide the IRQ control cap */
	write_slot((((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) + (seL4_CapIRQControl)),
		   cap_irq_control_cap_new());
}
/** This and only this function initialises the CPU.
 *
 * It does NOT initialise any kernel state.
 * @return For the verification build, this currently returns true always.
 */
static bool_t init_cpu(void)
{
	bool_t haveHWFPU;
	activate_kernel_vspace();

	/* Setup kernel stack pointer.
	 * On ARM SMP, the array index here is the CPU ID
	 */
	word_t stack_top = ((word_t)kernel_stack_alloc[0lu]) + (1ul << (12));
	setKernelStack(stack_top);
	/* initialise CPU's exception vector table */
	setVtable((pptr_t)arm_vector_table);
	haveHWFPU = fpsimd_HWCapTest();
	/* Disable FPU to avoid channels where a platform has an FPU but doesn't make use of it */
	if (haveHWFPU) {
		disableFpu();
	}
	if (haveHWFPU) {
		if (!fpsimd_init()) {
			return false;
		}
	} else {
		printf("Platform claims to have FP hardware, but does not!");
		return false;
	}
	cpu_initLocalIRQController();
	/* Export selected CPU features for access by PL0 */
	armv_init_user_access();
	initTimer();
	return true;
}
/* This and only this function initialises the platform. It does NOT initialise any kernel state. */
static void init_plat(void)
{
	initIRQController();
	initL2Cache();
}
/* Main kernel initialisation function. */
static bool_t try_init_kernel(paddr_t ui_p_reg_start, paddr_t ui_p_reg_end, sword_t pv_offset,
			      vptr_t v_entry, paddr_t dtb_phys_addr, word_t dtb_size)
{
	cap_t root_cnode_cap;
	cap_t it_ap_cap;
	cap_t it_pd_cap;
	cap_t ipcbuf_cap;
	p_region_t ui_p_reg = (p_region_t){ui_p_reg_start, ui_p_reg_end};
	region_t ui_reg = paddr_to_pptr_reg(ui_p_reg);
	word_t extra_bi_size = 0;
	pptr_t extra_bi_offset = 0;
	vptr_t extra_bi_frame_vptr;
	vptr_t bi_frame_vptr;
	vptr_t ipcbuf_vptr;
	create_frames_of_region_ret_t create_frames_ret;
	create_frames_of_region_ret_t extra_bi_ret;
	/* convert from physical addresses to userland vptrs */
	v_region_t ui_v_reg = {.start = ui_p_reg_start - pv_offset,
			       .end = ui_p_reg_end - pv_offset};
	ipcbuf_vptr = ui_v_reg.end;
	bi_frame_vptr = ipcbuf_vptr + (1ul << (12));
	extra_bi_frame_vptr = bi_frame_vptr + (1ul << (12));
	/* setup virtual memory for the kernel */
	map_kernel_window();
	/* initialise the CPU */
	if (!init_cpu()) {
		printf("ERROR: CPU init failed\n");
		return false;
	}
	/* debug output via serial port is only available from here */
	printf("Bootstrapping kernel\n");
	/* initialise the platform */
	init_plat();
	/* If a DTB was provided, pass the data on as extra bootinfo */
	p_region_t dtb_p_reg = (p_region_t){.start = 0, .end = 0};
	if (dtb_size > 0) {
		paddr_t dtb_phys_end = dtb_phys_addr + dtb_size;
		if (dtb_phys_end < dtb_phys_addr) {
			/* An integer overflow happened in DTB end address calculation, the
			 * location or size passed seems invalid.
			 */
			printf("ERROR: DTB location at %lx len %lu invalid\n", dtb_phys_addr,
			       dtb_size);
			return false;
		}
		/* If the DTB is located in physical memory that is not mapped in the
		 * kernel window we cannot access it.
		 */
		if (dtb_phys_end >= (PPTR_TOP - (PPTR_BASE - 0x0ul))) {
			printf("ERROR: DTB at [%lx..%lx] exceeds PADDR_TOP (%lx)\n", dtb_phys_addr,
			       dtb_phys_end, (PPTR_TOP - (PPTR_BASE - 0x0ul)));
			return false;
		}
		/* DTB seems valid and accessible, pass it on in bootinfo. */
		extra_bi_size += sizeof(seL4_BootInfoHeader) + dtb_size;
		/* Remember the memory region it uses. */
		dtb_p_reg = (p_region_t){.start = dtb_phys_addr, .end = dtb_phys_end};
	}
	/* The region of the initial thread is the user image + ipcbuf and boot info */
	word_t extra_bi_size_bits = calculate_extra_bi_size_bits(extra_bi_size);
	v_region_t it_v_reg = {.start = ui_v_reg.start,
			       .end = extra_bi_frame_vptr + (1ul << (extra_bi_size_bits))};
	if (it_v_reg.end >= 0x00007fffffffffff) {
		/* Variable arguments for printf() require well defined integer types to
		 * work properly. Unfortunately, the definition of USER_TOP differs
		 * between platforms (int, long), so we have to cast here to play safe.
		 */
		printf("ERROR: userland image virt [%lx..%lx]exceeds USER_TOP (%lx)\n",
		       it_v_reg.start, it_v_reg.end, (word_t)0x00007fffffffffff);
		return false;
	}
	if (!arch_init_freemem(ui_p_reg, dtb_p_reg, it_v_reg, extra_bi_size_bits)) {
		printf("ERROR: free memory management initialization failed\n");
		return false;
	}
	/* create the root cnode */
	root_cnode_cap = create_root_cnode();
	if (cap_get_capType(root_cnode_cap) == cap_null_cap) {
		printf("ERROR: root c-node creation failed\n");
		return false;
	}
	/* create the cap for managing thread domains */
	create_domain_cap(root_cnode_cap);
	/* initialise the IRQ states and provide the IRQ control cap */
	init_irqs(root_cnode_cap);
	populate_bi_frame(0, 1, ipcbuf_vptr, extra_bi_size);
	/* put DTB in the bootinfo block, if present. */
	seL4_BootInfoHeader header;
	if (dtb_size > 0) {
		header.id = SEL4_BOOTINFO_HEADER_FDT;
		header.len = sizeof(header) + dtb_size;
		*(seL4_BootInfoHeader *)(rootserver.extra_bi + extra_bi_offset) = header;
		extra_bi_offset += sizeof(header);
		memcpy((void *)(rootserver.extra_bi + extra_bi_offset), ptrFromPAddr(dtb_phys_addr),
		       dtb_size);
		extra_bi_offset += dtb_size;
	}
	if (extra_bi_size > extra_bi_offset) {
		/* provide a chunk for any leftover padding in the extended boot info */
		header.id = SEL4_BOOTINFO_HEADER_PADDING;
		header.len = (extra_bi_size - extra_bi_offset);
		*(seL4_BootInfoHeader *)(rootserver.extra_bi + extra_bi_offset) = header;
	}
	ndks_boot.bi_frame->ioSpaceCaps = (seL4_SlotRegion){.start = 0, .end = 0};
	/* Construct an initial address space with enough virtual addresses
	 * to cover the user image + ipc buffer and bootinfo frames */
	it_pd_cap = create_it_address_space(root_cnode_cap, it_v_reg);
	if (cap_get_capType(it_pd_cap) == cap_null_cap) {
		printf("ERROR: address space creation for initial thread failed\n");
		return false;
	}
	/* Create and map bootinfo frame cap */
	create_bi_frame_cap(root_cnode_cap, it_pd_cap, bi_frame_vptr);
	/* create and map extra bootinfo region */
	if (extra_bi_size > 0) {
		region_t extra_bi_region = {.start = rootserver.extra_bi,
					    .end = rootserver.extra_bi + extra_bi_size};
		extra_bi_ret = create_frames_of_region(
			root_cnode_cap, it_pd_cap, extra_bi_region, true,
			addrFromPPtr((void *)extra_bi_region.start) - extra_bi_frame_vptr);
		if (!extra_bi_ret.success) {
			printf("ERROR: mapping extra boot info to initial thread failed\n");
			return false;
		}
		ndks_boot.bi_frame->extraBIPages = extra_bi_ret.region;
	}
	/* create the initial thread's IPC buffer */
	ipcbuf_cap = create_ipcbuf_frame_cap(root_cnode_cap, it_pd_cap, ipcbuf_vptr);
	if (cap_get_capType(ipcbuf_cap) == cap_null_cap) {
		printf("ERROR: could not create IPC buffer for initial thread\n");
		return false;
	}
	/* create all userland image frames */
	create_frames_ret =
		create_frames_of_region(root_cnode_cap, it_pd_cap, ui_reg, true, pv_offset);
	if (!create_frames_ret.success) {
		printf("ERROR: could not create all userland image frames\n");
		return false;
	}
	ndks_boot.bi_frame->userImageFrames = create_frames_ret.region;
	/* create/initialise the initial thread's ASID pool */
	it_ap_cap = create_it_asid_pool(root_cnode_cap);
	if (cap_get_capType(it_ap_cap) == cap_null_cap) {
		printf("ERROR: could not create ASID pool for initial thread\n");
		return false;
	}
	write_it_asid_pool(it_ap_cap, it_pd_cap);
	/* create the idle thread */
	if (!create_idle_thread()) {
		printf("ERROR: could not create idle thread\n");
		return false;
	}
	/* Before creating the initial thread (which also switches to it)
	 * we clean the cache so that any page table information written
	 * as a result of calling create_frames_of_region will be correctly
	 * read by the hardware page table walker */
	cleanInvalidateL1Caches();
	/* create the initial thread */
	tcb_t *initial = create_initial_thread(root_cnode_cap, it_pd_cap, v_entry, bi_frame_vptr,
					       ipcbuf_vptr, ipcbuf_cap);
	if (initial == NULL) {
		printf("ERROR: could not create initial thread\n");
		return false;
	}
	init_core_state(initial);
	/* create all of the untypeds. Both devices and kernel window memory */
	if (!create_untypeds(root_cnode_cap, (region_t){KERNEL_ELF_BASE, (pptr_t)ki_boot_end}
			     /* reusable boot code/data */
			     )) {
		printf("ERROR: could not create untypteds for kernel image boot memory\n");
		return false;
	}
	/* no shared-frame caps (ARM has no multikernel support) */
	ndks_boot.bi_frame->sharedFrames = (seL4_SlotRegion){.start = 0, .end = 0};
	/* finalise the bootinfo frame */
	bi_finalise();
	/* Flushing the L1 cache and invalidating the TLB is good enough here to
	 * make sure everything written by the kernel is visible to userland. There
	 * are no uncached userland frames at this stage that require enforcing
	 * flushing to RAM. Any retyping operation will clean the memory down to RAM
	 * anyway.
	 */
	cleanInvalidateL1Caches();
	invalidateLocalTLB();
	ksNumCPUs = 1;
	/* initialize BKL before booting up other cores */
	/* All cores are up now, so there can be concurrency. The kernel booting is
	 * supposed to be finished before the secondary cores are released, all the
	 * primary has to do now is schedule the initial thread. Currently there is
	 * nothing that touches any global data structures, nevertheless we grab the
	 * BKL here to play safe. It is released when the kernel is left. */
	printf("Booting all finished, dropped to user space\n");
	/* kernel successfully initialized */
	return true;
}
void init_kernel(paddr_t ui_p_reg_start, paddr_t ui_p_reg_end, sword_t pv_offset, vptr_t v_entry,
		 paddr_t dtb_addr_p, uint32_t dtb_size)
{
	bool_t result;
	result = try_init_kernel(ui_p_reg_start, ui_p_reg_end, pv_offset, v_entry, dtb_addr_p,
				 dtb_size);
	if (!result) {
		_fail("ERROR: kernel init failed",
		      "/home/lab/projects/seL4/seL4test/kernel/src/arch/arm/kernel/boot.c", 651,
		      __func__);
		__builtin_unreachable();
	}
	schedule();
	activateThread();
}
void Arch_postModifyRegisters(tcb_t *tptr)
{
	/* Nothing to do */
}
/*
 * ARM L2 Cache controller L2C-310
 */
void initL2Cache(void);
void plat_cleanInvalidateL2Cache(void);
void plat_cleanCache(void);
void plat_cleanL2Range(paddr_t start, paddr_t end);
void plat_invalidateL2Range(paddr_t start, paddr_t end);
void plat_cleanInvalidateL2Range(paddr_t start, paddr_t end);
static void cleanCacheRange_PoC(vptr_t start, vptr_t end, paddr_t pstart)
{
	vptr_t line;
	word_t index;
	for (index = ((((start) >> (6)) << (6)) >> 6); index < ((((end) >> (6)) << (6)) >> 6) + 1;
	     index++) {
		line = index << 6;
		cleanByVA(line, pstart + (line - start));
	}
}
void cleanInvalidateCacheRange_RAM(vptr_t start, vptr_t end, paddr_t pstart)
{
	vptr_t line;
	word_t index;
	/** GHOSTUPD: "((gs_get_assn cap_get_capSizeBits_'proc \<acute>ghost'state = 0
		\<or> \<acute>end - \<acute>start <= gs_get_assn cap_get_capSizeBits_'proc
	   \<acute>ghost'state)
	    \<and> \<acute>start <= \<acute>end, id)" */
	/* First clean the L1 range */
	cleanCacheRange_PoC(start, end, pstart);
	/* ensure operation completes and visible in L2 */
	dsb();
	/* Now clean and invalidate the L2 range */
	plat_cleanInvalidateL2Range(pstart, pstart + (end - start));
	/* Finally clean and invalidate the L1 range. The extra clean is only strictly neccessary
	 * in a multiprocessor environment to prevent a write being lost if another core is
	 * attempting a store at the same time. As the range should already be clean asking
	 * it to clean again should not affect performance */
	for (index = ((((start) >> (6)) << (6)) >> 6); index < ((((end) >> (6)) << (6)) >> 6) + 1;
	     index++) {
		line = index << 6;
		cleanInvalByVA(line, pstart + (line - start));
	}
	/* ensure clean and invalidate complete */
	dsb();
}
void cleanCacheRange_RAM(vptr_t start, vptr_t end, paddr_t pstart)
{
	/** GHOSTUPD: "((gs_get_assn cap_get_capSizeBits_'proc \<acute>ghost'state = 0
		\<or> \<acute>end - \<acute>start <= gs_get_assn cap_get_capSizeBits_'proc
	   \<acute>ghost'state)
	    \<and> \<acute>start <= \<acute>end
	    \<and> \<acute>pstart <= \<acute>pstart + (\<acute>end - \<acute>start), id)" */
	/* clean l1 to l2 */
	cleanCacheRange_PoC(start, end, pstart);
	/* ensure cache operation completes before cleaning l2 */
	dsb();
	/** GHOSTUPD: "((gs_get_assn cap_get_capSizeBits_'proc \<acute>ghost'state = 0
		\<or> \<acute>end - \<acute>start <= gs_get_assn cap_get_capSizeBits_'proc
	   \<acute>ghost'state)
	    \<and> \<acute>start <= \<acute>end
	    \<and> \<acute>pstart <= \<acute>pstart + (\<acute>end - \<acute>start), id)" */
	/* now clean l2 to RAM */
	plat_cleanL2Range(pstart, pstart + (end - start));
}
void cleanCacheRange_PoU(vptr_t start, vptr_t end, paddr_t pstart)
{
	vptr_t line;
	word_t index;
	/** GHOSTUPD: "((gs_get_assn cap_get_capSizeBits_'proc \<acute>ghost'state = 0
		\<or> \<acute>end - \<acute>start <= gs_get_assn cap_get_capSizeBits_'proc
	   \<acute>ghost'state)
	    \<and> \<acute>start <= \<acute>end
	    \<and> \<acute>pstart <= \<acute>pstart + (\<acute>end - \<acute>start), id)" */
	for (index = ((((start) >> (6)) << (6)) >> 6); index < ((((end) >> (6)) << (6)) >> 6) + 1;
	     index++) {
		line = index << 6;
		cleanByVA_PoU(line, pstart + (line - start));
	}
}
void invalidateCacheRange_RAM(vptr_t start, vptr_t end, paddr_t pstart)
{
	vptr_t line;
	word_t index;
	/* If the start and end are not aligned to a cache line boundary
	 * then we need to clean the line first to prevent invalidating
	 * bytes we didn't mean to. Calling the functions in this way is
	 * not the most efficient method, but we assume the user will
	 * rarely be this silly */
	if (start != (((start) >> (6)) << (6))) {
		cleanCacheRange_RAM(start, start, pstart);
	}
	if (end + 1 != (((end + 1) >> (6)) << (6))) {
		line = (((end) >> (6)) << (6));
		cleanCacheRange_RAM(line, line, pstart + (line - start));
	}
	/** GHOSTUPD: "((gs_get_assn cap_get_capSizeBits_'proc \<acute>ghost'state = 0
		\<or> \<acute>end - \<acute>start <= gs_get_assn cap_get_capSizeBits_'proc
	   \<acute>ghost'state)
	    \<and> \<acute>start <= \<acute>end
	    \<and> \<acute>pstart <= \<acute>pstart + (\<acute>end - \<acute>start), id)" */
	/* Invalidate L2 range. Invalidating the L2 before the L1 is the order
	 * given in the l2c_310 manual, as an L1 line might be allocated from the L2
	 * before the L2 can be invalidated. */
	plat_invalidateL2Range(pstart, pstart + (end - start));
	/** GHOSTUPD: "((gs_get_assn cap_get_capSizeBits_'proc \<acute>ghost'state = 0
		\<or> \<acute>end - \<acute>start <= gs_get_assn cap_get_capSizeBits_'proc
	   \<acute>ghost'state)
	    \<and> \<acute>start <= \<acute>end
	    \<and> \<acute>pstart <= \<acute>pstart + (\<acute>end - \<acute>start), id)" */
	/* Now invalidate L1 range */
	for (index = ((((start) >> (6)) << (6)) >> 6); index < ((((end) >> (6)) << (6)) >> 6) + 1;
	     index++) {
		line = index << 6;
		invalidateByVA(line, pstart + (line - start));
	}
	/* Ensure invalidate completes */
	dsb();
}
void invalidateCacheRange_I(vptr_t start, vptr_t end, paddr_t pstart)
{
	vptr_t line;
	word_t index;
	for (index = ((((start) >> (6)) << (6)) >> 6); index < ((((end) >> (6)) << (6)) >> 6) + 1;
	     index++) {
		line = index << 6;
		invalidateByVA_I(line, pstart + (line - start));
	}
}
void branchFlushRange(vptr_t start, vptr_t end, paddr_t pstart)
{
	vptr_t line;
	word_t index;
	for (index = ((((start) >> (6)) << (6)) >> 6); index < ((((end) >> (6)) << (6)) >> 6) + 1;
	     index++) {
		line = index << 6;
		branchFlush(line, pstart + (line - start));
	}
}
void cleanCaches_PoU(void)
{
	dsb();
	clean_D_PoU();
	dsb();
	invalidate_I_PoU();
	dsb();
}
void cleanInvalidateL1Caches(void)
{
	dsb();
	cleanInvalidate_D_PoC();
	dsb();
	invalidate_I_PoU();
	dsb();
}
void arch_clean_invalidate_caches(void)
{
	cleanCaches_PoU();
	plat_cleanInvalidateL2Cache();
	cleanInvalidateL1Caches();
	isb();
}
void arch_clean_invalidate_L1_caches(word_t type)
{
	dsb();
	if (type & (1ul << (1))) {
		cleanInvalidate_L1D();
		dsb();
	}
	if (type & (1ul << (0))) {
		invalidate_I_PoU();
		dsb();
		isb();
	}
}
/* Prototyped here as this is referenced from assembly */
void arm_errata(void);
void arm_errata(void) {}
/* Use this to forward interrupts to all CPUs when debugging */
volatile struct gic_dist_map *const gic_dist =
	(volatile struct gic_dist_map *)(GIC_V2_DISTRIBUTOR_PPTR);
volatile struct gic_cpu_iface_map *const gic_cpuiface =
	(volatile struct gic_cpu_iface_map *)(GIC_V2_CONTROLLER_PPTR);
word_t active_irq[1] = {1023u};
/* Get the target id for this processor. We rely on the constraint that the registers
 * for PPI are read only and return only the current processor as the target.
 * If this doesn't lead to a valid ID, we emit a warning and default to core 0.
 */
static uint8_t infer_cpu_gic_id(int nirqs)
{
	word_t i;
	uint32_t target = 0;
	for (i = 0; i < nirqs; i += 4) {
		target = gic_dist->targets[i >> 2];
		target |= target >> 16;
		target |= target >> 8;
		if (target) {
			break;
		}
	}
	if (!target) {
		printf("Warning: Could not infer GIC interrupt target ID, assuming 0.\n");
		target = (1ul << (0));
	}
	return target & 0xff;
}
static void dist_init(void)
{
	word_t i;
	int nirqs = 32 * ((gic_dist->ic_type & 0x1f) + 1);
	gic_dist->enable = 0;
	for (i = 0; i < nirqs; i += 32) {
		/* disable */
		gic_dist->enable_clr[i >> 5] = 0xffffffff;
		/* clear pending */
		gic_dist->pending_clr[i >> 5] = 0xffffffff;
	}
	/* reset interrupts priority */
	for (i = 32; i < nirqs; i += 4) {
		gic_dist->priority[i >> 2] = 0;
	}
	/*
	 * reset int target to current cpu
	 * We query which id that the GIC uses for us and use that.
	 */
	uint8_t target = infer_cpu_gic_id(nirqs);
	for (i = 0; i < nirqs; i += 4) {
		gic_dist->targets[i >> 2] = ((((target)&0xff) << 0u) | (((target)&0xff) << 8u) |
					     (((target)&0xff) << 16u) | (((target)&0xff) << 24u));
	}
	/* level-triggered, 1-N */
	for (i = 64; i < nirqs; i += 32) {
		gic_dist->config[i >> 5] = 0x55555555;
	}
	/* group 0 for secure; group 1 for non-secure */
	for (i = 0; i < nirqs; i += 32) {
		if (0 && !/* KernelPlatformQEMUArmVirt=ON */ 1) {
			gic_dist->security[i >> 5] = 0xffffffff;
		} else {
			gic_dist->security[i >> 5] = 0;
		}
	}
	/* enable the int controller */
	gic_dist->enable = 1;
}
static void cpu_iface_init(void)
{
	uint32_t i;
	/* For non-Exynos4, the registers are banked per CPU, need to clear them */
	gic_dist->enable_clr[0] = 0xffffffff;
	gic_dist->pending_clr[0] = 0xffffffff;
	/* put everything in group 0; group 1 if in hyp mode */
	if (0 && !/* KernelPlatformQEMUArmVirt=ON */ 1) {
		gic_dist->security[0] = 0xffffffff;
		gic_dist->priority[0] = 0x80808080;
	} else {
		gic_dist->security[0] = 0;
		gic_dist->priority[0] = 0x0;
	}
	/* clear any software generated interrupts */
	for (i = 0; i < 16; i += 4) {
		gic_dist->sgi_pending_clr[i >> 2] = 0xffffffff;
	}
	gic_cpuiface->icontrol = 0;
	/* the write to priority mask is ignored if the kernel is
	 * in non-secure mode and the priority mask is already configured
	 * by secure mode software. the elfloader should config the
	 * interrupt routing properly to ensure that the hyp-mode kernel
	 * can get interrupts
	 */
	gic_cpuiface->pri_msk_c = 0x000000f0;
	gic_cpuiface->pb_c = 0x00000003;
	i = gic_cpuiface->int_ack;
	while ((i & ((1ul << (10u)) - 1ul)) != 1023u) {
		gic_cpuiface->eoi = i;
		i = gic_cpuiface->int_ack;
	}
	gic_cpuiface->icontrol = 1;
}
void setIRQTrigger(irq_t irq, bool_t trigger)
{
	/* in the gic_config, there is a 2 bit field for each irq,
	 * setting the most significant bit of this field makes the irq edge-triggered,
	 * while 0 indicates that it is level-triggered */
	word_t index = (irq) / 16u;
	word_t offset = ((irq) % 16u) * 2;
	if (trigger) {
		/* set the bit */
		gic_dist->config[index] |= (1ul << (offset + 1));
	} else {
		gic_dist->config[index] &= ~(1ul << (offset + 1));
	}
}
void initIRQController(void)
{
	/* irqInvalid cannot correspond to a valid IRQ index into the irq state array */
	dist_init();
}
void cpu_initLocalIRQController(void)
{
	cpu_iface_init();
}
word_t getRestartPC(tcb_t *thread)
{
	return getRegister(thread, FaultIP);
}
void setNextPC(tcb_t *thread, word_t v)
{
	setRegister(thread, ELR_EL1, v);
}
void map_kernel_devices(void)
{
	/* If there are no kernel device frames at all, then kernel_device_frames is
	 * NULL. Thus we can't use ARRAY_SIZE(kernel_device_frames) here directly,
	 * but have to use NUM_KERNEL_DEVICE_FRAMES that is defined accordingly.
	 */
	for (int i = 0; i < (sizeof(kernel_device_frames) / sizeof((kernel_device_frames)[0]));
	     i++) {
		const kernel_frame_t *frame = &kernel_device_frames[i];
		/* all frames are supposed to describe device memory, so they should
		 * never be marked as executable.
		 */
		map_kernel_frame(frame->paddr, frame->pptr, VMKernelOnly,
				 vm_attributes_new(frame->armExecuteNever, false, false));
		if (!frame->userAvailable) {
			reserve_region((p_region_t){.start = frame->paddr,
						    .end = frame->paddr + (1ul << (12))});
		}
	}
}
void uart_drv_putchar(unsigned char c);
static inline void uart_console_putchar(unsigned char c)
{
	/* UART console requires printing a '\r' (CR) before any '\n' (LF) */
	if (c == '\n') {
		uart_drv_putchar('\r');
	}
	uart_drv_putchar(c);
}
unsigned char uart_drv_getchar(void);
void kernel_putDebugChar(unsigned char c)
{
	uart_console_putchar(c);
}
unsigned char kernel_getDebugChar(void)
{
	return uart_drv_getchar();
}
void initL2Cache(void) {}
void plat_cleanL2Range(paddr_t start, paddr_t end) {}
void plat_invalidateL2Range(paddr_t start, paddr_t end) {}
void plat_cleanInvalidateL2Range(paddr_t start, paddr_t end) {}
void plat_cleanInvalidateL2Cache(void) {}
static exception_t Arch_invokeIRQControl(irq_t irq, cte_t *handlerSlot, cte_t *controlSlot,
					 bool_t trigger)
{
	setIRQTrigger(irq, trigger);
	return invokeIRQControl(irq, handlerSlot, controlSlot);
}
exception_t Arch_decodeIRQControlInvocation(word_t invLabel, word_t length, cte_t *srcSlot,
					    word_t *buffer)
{
	if (invLabel == ARMIRQIssueIRQHandlerTrigger) {
		if (length < 4 || current_extra_caps.excaprefs[0] == NULL) {
			current_syscall_error.type = seL4_TruncatedMessage;
			return EXCEPTION_SYSCALL_ERROR;
		}
		word_t irq_w = getSyscallArg(0, buffer);
		irq_t irq = (irq_t)(irq_w);
		bool_t trigger = !!getSyscallArg(1, buffer);
		word_t index = getSyscallArg(2, buffer);
		word_t depth = getSyscallArg(3, buffer);
		cap_t cnodeCap = current_extra_caps.excaprefs[0]->cap;
		exception_t status = Arch_checkIRQ(irq_w);
		if (status != EXCEPTION_NONE) {
			return status;
		}
		if (isIRQActive(irq)) {
			current_syscall_error.type = seL4_RevokeFirst;
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Rejecting request "
				       "for IRQ %u. Already active.>>\n",
				       0lu, __func__, 58, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread), (int)(irq));
			} while (0);
			return EXCEPTION_SYSCALL_ERROR;
		}
		lookupSlot_ret_t lu_ret = lookupTargetSlot(cnodeCap, index, depth);
		if (lu_ret.status != EXCEPTION_NONE) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Target slot for "
				       "new IRQ Handler cap invalid: cap %lu, IRQ %u.>>\n",
				       0lu, __func__, 64, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread), getExtraCPtr(buffer, 0),
				       (int)(irq));
			} while (0);
			return lu_ret.status;
		}
		cte_t *destSlot = lu_ret.slot;
		status = ensureEmptySlot(destSlot);
		if (status != EXCEPTION_NONE) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Target slot for "
				       "new IRQ Handler cap not empty: cap %lu, IRQ %u.>>\n",
				       0lu, __func__, 73, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread), getExtraCPtr(buffer, 0),
				       (int)(irq));
			} while (0);
			return status;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return Arch_invokeIRQControl(irq, destSlot, srcSlot, trigger);
	} else {
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
}
word_t Arch_decodeTransfer(word_t flags)
{
	return 0;
}
exception_t Arch_performTransfer(word_t arch, tcb_t *tcb_src, tcb_t *tcb_dest)
{
	return EXCEPTION_NONE;
}
void _fail(const char *s, const char *file, unsigned int line, const char *function)
{
	printf("seL4 called fail at %s:%u in function %s, saying \"%s\"\n", file, line, function,
	       s);
	halt();
}
void uart_drv_putchar(unsigned char c)
{
	while ((*((volatile uint32_t *)((0xffffffffffe00000ul + 0x0) + (0x018))) & (1ul << (5))) !=
	       0)
		;
	*((volatile uint32_t *)((0xffffffffffe00000ul + 0x0) + (0x000))) = c;
}
unsigned char uart_drv_getchar(void)
{
	while ((*((volatile uint32_t *)((0xffffffffffe00000ul + 0x0) + (0x018))) & (1ul << (4))) !=
	       0)
		;
	return *((volatile uint32_t *)((0xffffffffffe00000ul + 0x0) + (0x000)));
}
void initGenericTimer(void)
{
	if (/* KernelDebugBuild=ON */ 1) {
		/* check the frequency is correct */
		word_t gpt_cntfrq = 0;
		__asm__ volatile("mrs %x0,"
				 "cntfrq_el0"
				 : "=r"(gpt_cntfrq));
		/* The CNTFRQ register is a 32-bit register, its value can safely be
		 * compared with TIMER_CLOCK_HZ.
		 */
		if ((gpt_cntfrq != 0) && (gpt_cntfrq != 62500000llu)) {
			/* TIMER_CLOCK_HZ is defined as a unsigned long long constant on
			 * every architecture. */
			printf("Warning:  gpt_cntfrq %"
			       "lu"
			       ", expected %llu\n",
			       gpt_cntfrq, 62500000llu);
		}
	}
	resetTimer();
}
/*
 * The exynos5 platforms require custom hardware initialisation before the
 * generic timer is usable. They need to overwrite initTimer before calling
 * initGenericTimer because of this. We cannot use a `weak` symbol definition
 * in this case because the kernel is built as a single file and multiple
 * symbol definitions with the same name are not allowed. We therefore resort
 * to ifdef'ing out this initTimer definition for exynos5 platforms.
 */
void initTimer(void)
{
	initGenericTimer();
}
/* Fastpath cap lookup.  Returns a null_cap on failure. */
static inline cap_t lookup_fp(cap_t cap, cptr_t cptr)
{
	word_t cptr2;
	cte_t *slot;
	word_t guardBits, radixBits, bits;
	word_t radix, capGuard;
	bits = 0;
	if (__builtin_expect(!!(!cap_capType_equals(cap, cap_cnode_cap)), 0)) {
		return cap_null_cap_new();
	}
	do {
		guardBits = cap_cnode_cap_get_capCNodeGuardSize(cap);
		radixBits = cap_cnode_cap_get_capCNodeRadix(cap);
		cptr2 = cptr << bits;
		capGuard = cap_cnode_cap_get_capCNodeGuard(cap);
		/* Check the guard. Depth mismatch check is deferred.
		   The 32MinusGuardSize encoding contains an exception
		   when the guard is 0, when 32MinusGuardSize will be
		   reported as 0 also. In this case we skip the check */
		if (__builtin_expect(!!(guardBits), 1) &&
		    __builtin_expect(!!(cptr2 >> ((1 << 6) - guardBits) != capGuard), 0)) {
			return cap_null_cap_new();
		}
		radix = cptr2 << guardBits >> ((1 << 6) - radixBits);
		slot = ((cte_t *)(cap_cnode_cap_get_capCNodePtr(cap))) + radix;
		cap = slot->cap;
		bits += guardBits + radixBits;
	} while (
		__builtin_expect(!!(bits < (1 << 6) && cap_capType_equals(cap, cap_cnode_cap)), 0));
	if (__builtin_expect(!!(bits > (1 << 6)), 0)) {
		/* Depth mismatch. We've overshot wordBits bits. The lookup we've done is
		   safe, but wouldn't be allowed by the slowpath. */
		return cap_null_cap_new();
	}
	return cap;
}
/* make sure the fastpath functions conform with structure_*.bf */
static inline void thread_state_ptr_set_tsType_np(thread_state_t *ts_ptr, word_t tsType)
{
	ts_ptr->words[0] = tsType;
}
static inline void thread_state_ptr_mset_blockingObject_tsType(thread_state_t *ts_ptr,
							       word_t ep_ref, word_t tsType)
{
	ts_ptr->words[0] = ep_ref | tsType;
}
static inline void cap_reply_cap_ptr_new_np(cap_t *cap_ptr, word_t capReplyCanGrant,
					    word_t capReplyMaster, word_t capTCBPtr)
{
	cap_ptr->words[1] = (word_t)capTCBPtr;
	cap_ptr->words[0] =
		(capReplyMaster) | (capReplyCanGrant << 1) | ((word_t)cap_reply_cap << 59);
}
static inline void endpoint_ptr_mset_epQueue_tail_state(endpoint_t *ep_ptr, word_t epQueue_tail,
							word_t state)
{
	ep_ptr->words[0] = epQueue_tail | state;
}
static inline void endpoint_ptr_set_epQueue_head_np(endpoint_t *ep_ptr, word_t epQueue_head)
{
	ep_ptr->words[1] = epQueue_head;
}
static inline void fastpath_call(word_t cptr, word_t msgInfo)
{
	seL4_MessageInfo_t info;
	cap_t ep_cap;
	endpoint_t *ep_ptr;
	word_t length;
	tcb_t *dest;
	word_t badge;
	cap_t newVTable;
	vspace_root_t *cap_pd;
	pde_t stored_hw_asid;
	word_t fault_type;
	dom_t dom;
	/* Get message info, length, and fault type. */
	info = messageInfoFromWord_raw(msgInfo);
	length = seL4_MessageInfo_get_length(info);
	fault_type = seL4_Fault_get_seL4_FaultType(ksCurThread->tcbFault);
	/* Check there's no extra caps, the length is ok and there's no
	 * saved fault. */
	if (__builtin_expect(!!(fastpath_mi_check(msgInfo) || fault_type != seL4_Fault_NullFault),
			     0)) {
		slowpath(SysCall);
	}
	/* Lookup the cap */
	ep_cap = lookup_fp(
		(((cte_t *)((word_t)(ksCurThread) & ~((1ul << (11)) - 1ul))) + (tcbCTable))->cap,
		cptr);
	/* Check it's an endpoint */
	if (__builtin_expect(!!(!cap_capType_equals(ep_cap, cap_endpoint_cap) ||
				!cap_endpoint_cap_get_capCanSend(ep_cap)),
			     0)) {
		slowpath(SysCall);
	}
	/* Get the endpoint address */
	ep_ptr = ((endpoint_t *)(cap_endpoint_cap_get_capEPPtr(ep_cap)));
	/* Get the destination thread, which is only going to be valid
	 * if the endpoint is valid. */
	dest = ((tcb_t *)(endpoint_ptr_get_epQueue_head(ep_ptr)));
	/* Check that there's a thread waiting to receive */
	if (__builtin_expect(!!(endpoint_ptr_get_state(ep_ptr) != EPState_Recv), 0)) {
		slowpath(SysCall);
	}
	/* ensure we are not single stepping the destination in ia32 */
	/* Get destination thread.*/
	newVTable = (((cte_t *)((word_t)(dest) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap;
	/* Get vspace root. */
	cap_pd = ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(newVTable)));
	/* Ensure that the destination has a valid VTable. */
	if (__builtin_expect(!!(!isValidVTableRoot_fp(newVTable)), 0)) {
		slowpath(SysCall);
	}
	/* Need to test that the ASID is still valid */
	asid_t asid = cap_page_global_directory_cap_get_capPGDMappedASID(newVTable);
	asid_map_t asid_map = findMapForASID(asid);
	if (__builtin_expect(!!(asid_map_get_type(asid_map) != asid_map_asid_map_vspace ||
				((vspace_root_t *)(asid_map_asid_map_vspace_get_vspace_root(
					asid_map))) != cap_pd),
			     0)) {
		slowpath(SysCall);
	}
	stored_hw_asid.words[0] = asid;
	/* let gcc optimise this out for 1 domain */
	dom = maxDom ? ksCurDomain : 0;
	/* ensure only the idle thread or lower prio threads are present in the scheduler */
	if (__builtin_expect(!!(dest->tcbPriority < ksCurThread->tcbPriority &&
				!isHighestPrio(dom, dest->tcbPriority)),
			     0)) {
		slowpath(SysCall);
	}
	/* Ensure that the endpoint has has grant or grant-reply rights so that we can
	 * create the reply cap */
	if (__builtin_expect(!!(!cap_endpoint_cap_get_capCanGrant(ep_cap) &&
				!cap_endpoint_cap_get_capCanGrantReply(ep_cap)),
			     0)) {
		slowpath(SysCall);
	}
	/* Ensure the original caller is in the current domain and can be scheduled directly. */
	if (__builtin_expect(!!(dest->tcbDomain != ksCurDomain && 0 < maxDom), 0)) {
		slowpath(SysCall);
	}
	/*
	 * --- POINT OF NO RETURN ---
	 *
	 * At this stage, we have committed to performing the IPC.
	 */
	/* Dequeue the destination. */
	endpoint_ptr_set_epQueue_head_np(ep_ptr, ((word_t)(dest->tcbEPNext)));
	if (__builtin_expect(!!(dest->tcbEPNext), 0)) {
		dest->tcbEPNext->tcbEPPrev = NULL;
	} else {
		endpoint_ptr_mset_epQueue_tail_state(ep_ptr, 0, EPState_Idle);
	}
	badge = cap_endpoint_cap_get_capEPBadge(ep_cap);
	/* Unlink dest <-> reply, link src (cur thread) <-> reply */
	thread_state_ptr_set_tsType_np(&ksCurThread->tcbState, ThreadState_BlockedOnReply);
	/* Get sender reply slot */
	cte_t *replySlot =
		(((cte_t *)((word_t)(ksCurThread) & ~((1ul << (11)) - 1ul))) + (tcbReply));
	/* Get dest caller slot */
	cte_t *callerSlot = (((cte_t *)((word_t)(dest) & ~((1ul << (11)) - 1ul))) + (tcbCaller));
	/* Insert reply cap */
	word_t replyCanGrant = thread_state_ptr_get_blockingIPCCanGrant(&dest->tcbState);
	cap_reply_cap_ptr_new_np(&callerSlot->cap, replyCanGrant, 0, ((word_t)(ksCurThread)));
	mdb_node_ptr_set_mdbPrev_np(&callerSlot->cteMDBNode, ((word_t)(replySlot)));
	mdb_node_ptr_mset_mdbNext_mdbRevocable_mdbFirstBadged(&replySlot->cteMDBNode,
							      ((word_t)(callerSlot)), 1, 1);
	fastpath_copy_mrs(length, ksCurThread, dest);
	/* Dest thread is set Running, but not queued. */
	thread_state_ptr_set_tsType_np(&dest->tcbState, ThreadState_Running);
	switchToThread_fp(dest, cap_pd, stored_hw_asid);
	msgInfo = wordFromMessageInfo(seL4_MessageInfo_set_capsUnwrapped(info, 0));
	fastpath_restore(badge, msgInfo, ksCurThread);
}
static inline void fastpath_reply_recv(word_t cptr, word_t msgInfo)
{
	seL4_MessageInfo_t info;
	cap_t ep_cap;
	endpoint_t *ep_ptr;
	word_t length;
	tcb_t *caller;
	word_t badge;
	tcb_t *endpointTail;
	word_t fault_type;
	cap_t newVTable;
	vspace_root_t *cap_pd;
	pde_t stored_hw_asid;
	dom_t dom;
	/* Get message info and length */
	info = messageInfoFromWord_raw(msgInfo);
	length = seL4_MessageInfo_get_length(info);
	fault_type = seL4_Fault_get_seL4_FaultType(ksCurThread->tcbFault);
	/* Check there's no extra caps, the length is ok and there's no
	 * saved fault. */
	if (__builtin_expect(!!(fastpath_mi_check(msgInfo) || fault_type != seL4_Fault_NullFault),
			     0)) {
		slowpath(SysReplyRecv);
	}
	/* Lookup the cap */
	ep_cap = lookup_fp(
		(((cte_t *)((word_t)(ksCurThread) & ~((1ul << (11)) - 1ul))) + (tcbCTable))->cap,
		cptr);
	/* Check it's an endpoint */
	if (__builtin_expect(!!(!cap_capType_equals(ep_cap, cap_endpoint_cap) ||
				!cap_endpoint_cap_get_capCanReceive(ep_cap)),
			     0)) {
		slowpath(SysReplyRecv);
	}
	/* Check there is nothing waiting on the notification */
	if (__builtin_expect(!!(ksCurThread->tcbBoundNotification &&
				notification_ptr_get_state(ksCurThread->tcbBoundNotification) ==
					NtfnState_Active),
			     0)) {
		slowpath(SysReplyRecv);
	}
	/* Get the endpoint address */
	ep_ptr = ((endpoint_t *)(cap_endpoint_cap_get_capEPPtr(ep_cap)));
	/* Check that there's not a thread waiting to send */
	if (__builtin_expect(!!(endpoint_ptr_get_state(ep_ptr) == EPState_Send), 0)) {
		slowpath(SysReplyRecv);
	}
	/* Only reply if the reply cap is valid. */
	cte_t *callerSlot =
		(((cte_t *)((word_t)(ksCurThread) & ~((1ul << (11)) - 1ul))) + (tcbCaller));
	cap_t callerCap = callerSlot->cap;
	if (__builtin_expect(!!(!fastpath_reply_cap_check(callerCap)), 0)) {
		slowpath(SysReplyRecv);
	}
	/* Determine who the caller is. */
	caller = ((tcb_t *)(cap_reply_cap_get_capTCBPtr(callerCap)));
	/* ensure we are not single stepping the caller in ia32 */
	/* Check that the caller has not faulted, in which case a fault
	   reply is generated instead. */
	fault_type = seL4_Fault_get_seL4_FaultType(caller->tcbFault);
	if (__builtin_expect(!!(fault_type != seL4_Fault_NullFault), 0)) {
		slowpath(SysReplyRecv);
	}
	/* Get destination thread.*/
	newVTable = (((cte_t *)((word_t)(caller) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap;
	/* Get vspace root. */
	cap_pd = ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(newVTable)));
	/* Ensure that the destination has a valid MMU. */
	if (__builtin_expect(!!(!isValidVTableRoot_fp(newVTable)), 0)) {
		slowpath(SysReplyRecv);
	}
	/* Need to test that the ASID is still valid */
	asid_t asid = cap_page_global_directory_cap_get_capPGDMappedASID(newVTable);
	asid_map_t asid_map = findMapForASID(asid);
	if (__builtin_expect(!!(asid_map_get_type(asid_map) != asid_map_asid_map_vspace ||
				((vspace_root_t *)(asid_map_asid_map_vspace_get_vspace_root(
					asid_map))) != cap_pd),
			     0)) {
		slowpath(SysReplyRecv);
	}
	stored_hw_asid.words[0] = asid;
	/* Ensure the original caller can be scheduled directly. */
	dom = maxDom ? ksCurDomain : 0;
	if (__builtin_expect(!!(!isHighestPrio(dom, caller->tcbPriority)), 0)) {
		slowpath(SysReplyRecv);
	}
	/* Ensure the original caller is in the current domain and can be scheduled directly. */
	if (__builtin_expect(!!(caller->tcbDomain != ksCurDomain && 0 < maxDom), 0)) {
		slowpath(SysReplyRecv);
	}
	/*
	 * --- POINT OF NO RETURN ---
	 *
	 * At this stage, we have committed to performing the IPC.
	 */
	/* Set thread state to BlockedOnReceive */
	thread_state_ptr_mset_blockingObject_tsType(&ksCurThread->tcbState, (word_t)ep_ptr,
						    ThreadState_BlockedOnReceive);
	thread_state_ptr_set_blockingIPCCanGrant(&ksCurThread->tcbState,
						 cap_endpoint_cap_get_capCanGrant(ep_cap));
	/* Place the thread in the endpoint queue */
	endpointTail = ((tcb_t *)(endpoint_ptr_get_epQueue_tail(ep_ptr)));
	if (__builtin_expect(!!(!endpointTail), 1)) {
		ksCurThread->tcbEPPrev = NULL;
		ksCurThread->tcbEPNext = NULL;
		/* Set head/tail of queue and endpoint state. */
		endpoint_ptr_set_epQueue_head_np(ep_ptr, ((word_t)(ksCurThread)));
		endpoint_ptr_mset_epQueue_tail_state(ep_ptr, ((word_t)(ksCurThread)), EPState_Recv);
	} else {
		/* Append current thread onto the queue. */
		endpointTail->tcbEPNext = ksCurThread;
		ksCurThread->tcbEPPrev = endpointTail;
		ksCurThread->tcbEPNext = NULL;
		/* Update tail of queue. */
		endpoint_ptr_mset_epQueue_tail_state(ep_ptr, ((word_t)(ksCurThread)), EPState_Recv);
	}
	/* Delete the reply cap. */
	mdb_node_ptr_mset_mdbNext_mdbRevocable_mdbFirstBadged(
		&((cte_t *)(mdb_node_get_mdbPrev(callerSlot->cteMDBNode)))->cteMDBNode, 0, 1, 1);
	callerSlot->cap = cap_null_cap_new();
	callerSlot->cteMDBNode = mdb_node_new(0, false, false, 0);
	/* I know there's no fault, so straight to the transfer. */
	/* Replies don't have a badge. */
	badge = 0;
	fastpath_copy_mrs(length, ksCurThread, caller);
	/* Dest thread is set Running, but not queued. */
	thread_state_ptr_set_tsType_np(&caller->tcbState, ThreadState_Running);
	switchToThread_fp(caller, cap_pd, stored_hw_asid);
	msgInfo = wordFromMessageInfo(seL4_MessageInfo_set_capsUnwrapped(info, 0));
	fastpath_restore(badge, msgInfo, ksCurThread);
}
lookup_fault_t current_lookup_fault;
seL4_Fault_t current_fault;
syscall_error_t current_syscall_error;
/* (node-local) state accessed only during bootstrapping */
ndks_boot_t ndks_boot;
rootserver_mem_t rootserver;
static region_t rootserver_mem;
static void merge_regions(void)
{
	/* Walk through reserved regions and see if any can be merged */
	for (word_t i = 1; i < ndks_boot.resv_count;) {
		if (ndks_boot.reserved[i - 1].end == ndks_boot.reserved[i].start) {
			/* extend earlier region */
			ndks_boot.reserved[i - 1].end = ndks_boot.reserved[i].end;
			/* move everything else down */
			for (word_t j = i + 1; j < ndks_boot.resv_count; j++) {
				ndks_boot.reserved[j - 1] = ndks_boot.reserved[j];
			}
			ndks_boot.resv_count--;
			/* don't increment i in case there are multiple adjacent regions */
		} else {
			i++;
		}
	}
}
bool_t reserve_region(p_region_t reg)
{
	word_t i;
	if (reg.start == reg.end) {
		return true;
	}
	/* keep the regions in order */
	for (i = 0; i < ndks_boot.resv_count; i++) {
		/* Try and merge the region to an existing one, if possible */
		if (ndks_boot.reserved[i].start == reg.end) {
			ndks_boot.reserved[i].start = reg.start;
			merge_regions();
			return true;
		}
		if (ndks_boot.reserved[i].end == reg.start) {
			ndks_boot.reserved[i].end = reg.end;
			merge_regions();
			return true;
		}
		/* Otherwise figure out where it should go. */
		if (ndks_boot.reserved[i].start > reg.end) {
			/* move regions down, making sure there's enough room */
			if (ndks_boot.resv_count + 1 >=
			    (((sizeof(avail_p_regs) / sizeof((avail_p_regs)[0])) + 0 + 1 + 1) +
			     (sizeof(kernel_device_frames) / sizeof((kernel_device_frames)[0])) +
			     (3 + 0))) {
				printf("Can't mark region 0x%"
				       "lx"
				       "-0x%"
				       "lx"
				       " as reserved, try increasing MAX_NUM_RESV_REG (currently "
				       "%d)\n",
				       reg.start, reg.end,
				       (int)(((sizeof(avail_p_regs) / sizeof((avail_p_regs)[0])) +
					      0 + 1 + 1) +
					     (sizeof(kernel_device_frames) /
					      sizeof((kernel_device_frames)[0])) +
					     (3 + 0)));
				return false;
			}
			for (word_t j = ndks_boot.resv_count; j > i; j--) {
				ndks_boot.reserved[j] = ndks_boot.reserved[j - 1];
			}
			/* insert the new region */
			ndks_boot.reserved[i] = reg;
			ndks_boot.resv_count++;
			return true;
		}
	}
	if (i + 1 ==
	    (((sizeof(avail_p_regs) / sizeof((avail_p_regs)[0])) + 0 + 1 + 1) +
	     (sizeof(kernel_device_frames) / sizeof((kernel_device_frames)[0])) + (3 + 0))) {
		printf("Can't mark region 0x%"
		       "lx"
		       "-0x%"
		       "lx"
		       " as reserved, try increasing MAX_NUM_RESV_REG (currently %d)\n",
		       reg.start, reg.end,
		       (int)(((sizeof(avail_p_regs) / sizeof((avail_p_regs)[0])) + 0 + 1 + 1) +
			     (sizeof(kernel_device_frames) / sizeof((kernel_device_frames)[0])) +
			     (3 + 0)));
		return false;
	}
	ndks_boot.reserved[i] = reg;
	ndks_boot.resv_count++;
	return true;
}
static bool_t insert_region(region_t reg)
{
	if (is_reg_empty(reg)) {
		return true;
	}
	for (word_t i = 0; i < (sizeof(ndks_boot.freemem) / sizeof((ndks_boot.freemem)[0])); i++) {
		if (is_reg_empty(ndks_boot.freemem[i])) {
			reserve_region(pptr_to_paddr_reg(reg));
			ndks_boot.freemem[i] = reg;
			return true;
		}
	}
	/* We don't know if a platform or architecture picked MAX_NUM_FREEMEM_REG
	 * arbitrarily or carefully calculated it to be big enough. Running out of
	 * slots here is not really fatal, eventually memory allocation may fail
	 * if there is not enough free memory. However, allocations should never
	 * blindly assume to work, some error handling must always be in place even
	 * if the environment has been crafted carefully to support them. Thus, we
	 * don't stop the boot process here, but return an error. The caller should
	 * decide how bad this is.
	 */
	printf("no free memory slot left for [%"
	       "lx"
	       "..%"
	       "lx"
	       "],"
	       " consider increasing MAX_NUM_FREEMEM_REG (%u)\n",
	       reg.start, reg.end,
	       (unsigned int)((sizeof(avail_p_regs) / sizeof((avail_p_regs)[0])) + 0 + 1 + 1));
	/* For debug builds we consider this a fatal error. Rationale is, that the
	 * caller does not check the error code at the moment, but just ignores any
	 * failures silently. */
	return false;
}
static pptr_t alloc_rootserver_obj(word_t size_bits, word_t n)
{
	pptr_t allocated = rootserver_mem.start;
	/* allocated memory must be aligned */
	rootserver_mem.start += (n * (1ul << (size_bits)));
	/* we must not have run out of memory */
	memzero((void *)allocated, n * (1ul << (size_bits)));
	return allocated;
}
static word_t rootserver_max_size_bits(word_t extra_bi_size_bits)
{
	word_t cnode_size_bits = 13 + 5;
	word_t max = (((cnode_size_bits) > (12)) ? (cnode_size_bits) : (12));
	return (((max) > (extra_bi_size_bits)) ? (max) : (extra_bi_size_bits));
}
static word_t calculate_rootserver_size(v_region_t it_v_reg, word_t extra_bi_size_bits)
{
	/* work out how much memory we need for root server objects */
	word_t size = (1ul << (13 + 5));
	size += (1ul << (11)); // root thread tcb
	size += (1ul << (12)); // ipc buf
	size += (1ul << (12)); // boot info
	size += (1ul << (12));
	size += extra_bi_size_bits > 0 ? (1ul << (extra_bi_size_bits)) : 0;
	size += (1ul << (12)); // root vspace
	/* for all archs, seL4_PageTable Bits is the size of all non top-level paging structures */
	return size + arch_get_n_paging(it_v_reg) * (1ul << (12));
}
static void maybe_alloc_extra_bi(word_t cmp_size_bits, word_t extra_bi_size_bits)
{
	if (extra_bi_size_bits >= cmp_size_bits && rootserver.extra_bi == 0) {
		rootserver.extra_bi = alloc_rootserver_obj(extra_bi_size_bits, 1);
	}
}
/* Create pptrs for all root server objects, starting at a give start address,
 * to cover the virtual memory region v_reg, and any extra boot info.
 */
static void create_rootserver_objects(pptr_t start, v_region_t it_v_reg, word_t extra_bi_size_bits)
{
	/* the largest object the PD, the root cnode, or the extra boot info */
	word_t cnode_size_bits = 13 + 5;
	word_t max = rootserver_max_size_bits(extra_bi_size_bits);
	word_t size = calculate_rootserver_size(it_v_reg, extra_bi_size_bits);
	rootserver_mem.start = start;
	rootserver_mem.end = start + size;
	maybe_alloc_extra_bi(max, extra_bi_size_bits);
	/* the root cnode is at least 4k, so it could be larger or smaller than a pd. */
	rootserver.cnode = alloc_rootserver_obj(cnode_size_bits, 1);
	maybe_alloc_extra_bi(12, extra_bi_size_bits);
	rootserver.vspace = alloc_rootserver_obj(12, 1);
	/* at this point we are up to creating 4k objects - which is the min size of
	 * extra_bi so this is the last chance to allocate it */
	maybe_alloc_extra_bi(12, extra_bi_size_bits);
	_Static_assert(12 == 12, "invalid_seL4_ASIDPoolBits");
	rootserver.asid_pool = alloc_rootserver_obj(12, 1);
	rootserver.ipc_buf = alloc_rootserver_obj(12, 1);
	_Static_assert(12 == 12, "invalid_BI_FRAME_SIZE_BITS");
	rootserver.boot_info = alloc_rootserver_obj(12, 1);
	/* TCBs on aarch32 can be larger than page tables in certain configs */
	/* paging structures are 4k on every arch except aarch32 (1k) */
	word_t n = arch_get_n_paging(it_v_reg);
	rootserver.paging.start = alloc_rootserver_obj(12, n);
	rootserver.paging.end = rootserver.paging.start + n * (1ul << (12));
	/* for most archs, TCBs are smaller than page tables */
	rootserver.tcb = alloc_rootserver_obj(11, 1);
	/* we should have allocated all our memory */
}
void write_slot(slot_ptr_t slot_ptr, cap_t cap)
{
	slot_ptr->cap = cap;
	slot_ptr->cteMDBNode = mdb_node_new(0, false, false, 0);
	mdb_node_ptr_set_mdbRevocable(&slot_ptr->cteMDBNode, true);
	mdb_node_ptr_set_mdbFirstBadged(&slot_ptr->cteMDBNode, true);
}
/* Our root CNode needs to be able to fit all the initial caps and not
 * cover all of memory.
 */
_Static_assert(13 < 32 - 5 && (1ul << (13)) >= seL4_NumInitialCaps && (1ul << (13)) >= (12 - 5),
	       "root_cnode_size_valid");
cap_t create_root_cnode(void)
{
	cap_t cap = cap_cnode_cap_new(13,		 /* radix */
				      (1 << 6) - 13,	 /* guard size */
				      0,		 /* guard */
				      rootserver.cnode); /* pptr */
	/* write the root CNode cap into the root CNode */
	write_slot((((slot_ptr_t)(rootserver.cnode)) + (seL4_CapInitThreadCNode)), cap);
	return cap;
}
/* Check domain scheduler assumptions. */
_Static_assert(1 >= 1 && 1 <= 256, "num_domains_valid");
_Static_assert(256 >= 1 && 256 <= 256, "num_priorities_valid");
void create_domain_cap(cap_t root_cnode_cap)
{
	/* Check domain scheduler assumptions. */
	for (word_t i = 0; i < ksDomScheduleLength; i++) {
	}
	cap_t cap = cap_domain_cap_new();
	write_slot((((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) + (seL4_CapDomain)),
		   cap);
}
cap_t create_ipcbuf_frame_cap(cap_t root_cnode_cap, cap_t pd_cap, vptr_t vptr)
{
	clearMemory((void *)rootserver.ipc_buf, 12);
	/* create a cap of it and write it into the root CNode */
	cap_t cap = create_mapped_it_frame_cap(pd_cap, rootserver.ipc_buf, vptr,
					       1 /* initial thread's ASID */, false, false);
	write_slot((((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) +
		    (seL4_CapInitThreadIPCBuffer)),
		   cap);
	return cap;
}
void create_bi_frame_cap(cap_t root_cnode_cap, cap_t pd_cap, vptr_t vptr)
{
	/* create a cap of it and write it into the root CNode */
	cap_t cap = create_mapped_it_frame_cap(pd_cap, rootserver.boot_info, vptr,
					       1 /* initial thread's ASID */, false, false);
	write_slot(
		(((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) + (seL4_CapBootInfoFrame)),
		cap);
}
word_t calculate_extra_bi_size_bits(word_t extra_size)
{
	if (extra_size == 0) {
		return 0;
	}
	word_t clzl_ret = clzl((((((extra_size)-1ul) >> (12)) + 1ul) << (12)));
	word_t msb = (sizeof(seL4_Word) * 8) - 1 - clzl_ret;
	/* If region is bigger than a page, make sure we overallocate rather than
	 * underallocate
	 */
	if (extra_size > (1ul << (msb))) {
		msb++;
	}
	return msb;
}
void populate_bi_frame(node_id_t node_id, word_t num_nodes, vptr_t ipcbuf_vptr,
		       word_t extra_bi_size)
{
	/* clear boot info memory */
	clearMemory((void *)rootserver.boot_info, 12);
	if (extra_bi_size) {
		clearMemory((void *)rootserver.extra_bi,
			    calculate_extra_bi_size_bits(extra_bi_size));
	}
	/* initialise bootinfo-related global state */
	seL4_BootInfo *bi = ((seL4_BootInfo *)(rootserver.boot_info));
	bi->nodeID = node_id;
	bi->numNodes = num_nodes;
	bi->numIOPTLevels = 0;
	bi->ipcBuffer = (seL4_IPCBuffer *)ipcbuf_vptr;
	bi->initThreadCNodeSizeBits = 13;
	bi->initThreadDomain = ksDomSchedule[ksDomScheduleIdx].domain;
	bi->extraLen = extra_bi_size;
	ndks_boot.bi_frame = bi;
	ndks_boot.slot_pos_cur = seL4_NumInitialCaps;
}
bool_t provide_cap(cap_t root_cnode_cap, cap_t cap)
{
	if (ndks_boot.slot_pos_cur >= (1ul << (13))) {
		printf("ERROR: can't add another cap, all %"
		       "lu"
		       " (=2^CONFIG_ROOT_CNODE_SIZE_BITS) slots used\n",
		       (1ul << (13)));
		return false;
	}
	write_slot(
		(((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) + (ndks_boot.slot_pos_cur)),
		cap);
	ndks_boot.slot_pos_cur++;
	return true;
}
create_frames_of_region_ret_t create_frames_of_region(cap_t root_cnode_cap, cap_t pd_cap,
						      region_t reg, bool_t do_map,
						      sword_t pv_offset)
{
	pptr_t f;
	cap_t frame_cap;
	seL4_SlotPos slot_pos_before;
	seL4_SlotPos slot_pos_after;
	slot_pos_before = ndks_boot.slot_pos_cur;
	for (f = reg.start; f < reg.end; f += (1ul << (12))) {
		if (do_map) {
			frame_cap = create_mapped_it_frame_cap(
				pd_cap, f, addrFromPPtr((void *)(f - pv_offset)),
				1 /* initial thread's ASID */, false, true);
		} else {
			frame_cap = create_unmapped_it_frame_cap(f, false);
		}
		if (!provide_cap(root_cnode_cap, frame_cap)) {
			return (create_frames_of_region_ret_t){
				.region = (seL4_SlotRegion){.start = 0, .end = 0},
				.success = false};
		}
	}
	slot_pos_after = ndks_boot.slot_pos_cur;
	return (create_frames_of_region_ret_t){
		.region = (seL4_SlotRegion){.start = slot_pos_before, .end = slot_pos_after},
		.success = true};
}
cap_t create_it_asid_pool(cap_t root_cnode_cap)
{
	cap_t ap_cap = cap_asid_pool_cap_new(1 /* initial thread's ASID */ >> asidLowBits,
					     rootserver.asid_pool);
	write_slot((((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) +
		    (seL4_CapInitThreadASIDPool)),
		   ap_cap);
	/* create ASID control cap */
	write_slot((((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) + (seL4_CapASIDControl)),
		   cap_asid_control_cap_new());
	return ap_cap;
}
bool_t create_idle_thread(void)
{
	pptr_t pptr;
	pptr = (pptr_t)&ksIdleThreadTCB[0];
	ksIdleThread = ((tcb_t *)(pptr + (1ul << ((11 - 1)))));
	configureIdleThread(ksIdleThread);
	setThreadName(ksIdleThread, "idle_thread");
	return true;
}
tcb_t *create_initial_thread(cap_t root_cnode_cap, cap_t it_pd_cap, vptr_t ui_v_entry,
			     vptr_t bi_frame_vptr, vptr_t ipcbuf_vptr, cap_t ipcbuf_cap)
{
	tcb_t *tcb = ((tcb_t *)(rootserver.tcb + (1ul << ((11 - 1)))));
	tcb->tcbTimeSlice = 5;
	Arch_initContext(&tcb->tcbArch.tcbContext);
	/* derive a copy of the IPC buffer cap for inserting */
	deriveCap_ret_t dc_ret = deriveCap((((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) +
					    (seL4_CapInitThreadIPCBuffer)),
					   ipcbuf_cap);
	if (dc_ret.status != EXCEPTION_NONE) {
		printf("Failed to derive copy of IPC Buffer\n");
		return NULL;
	}
	/* initialise TCB (corresponds directly to abstract specification) */
	cteInsert(root_cnode_cap,
		  (((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) +
		   (seL4_CapInitThreadCNode)),
		  (((slot_ptr_t)(rootserver.tcb)) + (tcbCTable)));
	cteInsert(it_pd_cap,
		  (((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) +
		   (seL4_CapInitThreadVSpace)),
		  (((slot_ptr_t)(rootserver.tcb)) + (tcbVTable)));
	cteInsert(dc_ret.cap,
		  (((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) +
		   (seL4_CapInitThreadIPCBuffer)),
		  (((slot_ptr_t)(rootserver.tcb)) + (tcbBuffer)));
	tcb->tcbIPCBuffer = ipcbuf_vptr;
	setRegister(tcb, capRegister, bi_frame_vptr);
	setNextPC(tcb, ui_v_entry);
	/* initialise TCB */
	tcb->tcbPriority = seL4_MaxPrio;
	tcb->tcbMCP = seL4_MaxPrio;
	tcb->tcbDomain = ksDomSchedule[ksDomScheduleIdx].domain;
	setupReplyMaster(tcb);
	setThreadState(tcb, ThreadState_Running);
	ksCurDomain = ksDomSchedule[ksDomScheduleIdx].domain;
	ksDomainTime = ksDomSchedule[ksDomScheduleIdx].length;
	/* create initial thread's TCB cap */
	cap_t cap = cap_thread_cap_new(((word_t)(tcb)));
	write_slot(
		(((slot_ptr_t)((pptr_t)cap_get_capPtr(root_cnode_cap))) + (seL4_CapInitThreadTCB)),
		cap);
	setThreadName(tcb, "rootserver");
	return tcb;
}
void init_core_state(tcb_t *scheduler_action)
{
	ksActiveFPUState = NULL;
	/* add initial threads to the debug queue */
	ksDebugTCBs = NULL;
	if (scheduler_action != ((tcb_t *)0) && scheduler_action != ((tcb_t *)1)) {
		tcbDebugAppend(scheduler_action);
	}
	tcbDebugAppend(ksIdleThread);
	ksSchedulerAction = scheduler_action;
	ksCurThread = ksIdleThread;
}
static bool_t provide_untyped_cap(cap_t root_cnode_cap, bool_t device_memory, pptr_t pptr,
				  word_t size_bits, seL4_SlotPos first_untyped_slot)
{
	bool_t ret;
	cap_t ut_cap;
	word_t i = ndks_boot.slot_pos_cur - first_untyped_slot;
	if (i < 230) {
		ndks_boot.bi_frame->untypedList[i] =
			(seL4_UntypedDesc){.paddr = addrFromPPtr((void *)pptr),
					   .sizeBits = size_bits,
					   .isDevice = device_memory,
					   .padding = {0}};
		ut_cap = cap_untyped_cap_new(((1ul << ((size_bits)-4))), device_memory, size_bits,
					     pptr);
		ret = provide_cap(root_cnode_cap, ut_cap);
	} else {
		printf("Kernel init: Too many untyped regions for boot info\n");
		ret = true;
	}
	return ret;
}
static bool_t create_untypeds_for_region(cap_t root_cnode_cap, bool_t device_memory, region_t reg,
					 seL4_SlotPos first_untyped_slot)
{
	while (!is_reg_empty(reg)) {
		/* Calculate the bit size of the region. */
		unsigned int size_bits = (sizeof(seL4_Word) * 8) - 1 - clzl(reg.end - reg.start);
		/* The size can't exceed the largest possible untyped size. */
		if (size_bits > 47) {
			size_bits = 47;
		}
		/* The start address 0 satisfies any alignment needs, otherwise ensure
		 * the region's bit size does not exceed the alignment of the region.
		 */
		if (0 != reg.start) {
			unsigned int align_bits = ctzl(reg.start);
			if (size_bits > align_bits) {
				size_bits = align_bits;
			}
		}
		/* Provide an untyped capability for the region only if it is large
		 * enough to be retyped into objects later. Otherwise the region can't
		 * be used anyway.
		 */
		if (size_bits >= 4) {
			if (!provide_untyped_cap(root_cnode_cap, device_memory, reg.start,
						 size_bits, first_untyped_slot)) {
				return false;
			}
		}
		reg.start += (1ul << (size_bits));
	}
	return true;
}
bool_t create_untypeds(cap_t root_cnode_cap, region_t boot_mem_reuse_reg)
{
	seL4_SlotPos first_untyped_slot = ndks_boot.slot_pos_cur;
	paddr_t start = 0;
	for (word_t i = 0; i < ndks_boot.resv_count; i++) {
		if (start < ndks_boot.reserved[i].start) {
			region_t reg =
				paddr_to_pptr_reg((p_region_t){start, ndks_boot.reserved[i].start});
			if (!create_untypeds_for_region(root_cnode_cap, true, reg,
							first_untyped_slot)) {
				printf("ERROR: creation of untypeds for device region #%u at "
				       "[%lx..%lx] failed\n",
				       (unsigned int)i, reg.start, reg.end);
				return false;
			}
		}
		start = ndks_boot.reserved[i].end;
	}
	if (start < CONFIG_PADDR_USER_DEVICE_TOP) {
		region_t reg = paddr_to_pptr_reg((p_region_t){start, CONFIG_PADDR_USER_DEVICE_TOP});
		if (!create_untypeds_for_region(root_cnode_cap, true, reg, first_untyped_slot)) {
			printf("ERROR: creation of untypeds for top device region [%lx..%lx] "
			       "failed\n",
			       reg.start, reg.end);
			return false;
		}
	}
	/* if boot_mem_reuse_reg is not empty, we can create UT objs from boot code/data frames */
	if (!create_untypeds_for_region(root_cnode_cap, false, boot_mem_reuse_reg,
					first_untyped_slot)) {
		printf("ERROR: creation of untypeds for recycled boot memory [%lx..%lx] failed\n",
		       boot_mem_reuse_reg.start, boot_mem_reuse_reg.end);
		return false;
	}
	/* convert remaining freemem into UT objects and provide the caps */
	for (word_t i = 0; i < (sizeof(ndks_boot.freemem) / sizeof((ndks_boot.freemem)[0])); i++) {
		region_t reg = ndks_boot.freemem[i];
		ndks_boot.freemem[i] = (region_t){.start = 0, .end = 0};
		if (!create_untypeds_for_region(root_cnode_cap, false, reg, first_untyped_slot)) {
			printf("ERROR: creation of untypeds for free memory region #%u at "
			       "[%lx..%lx] failed\n",
			       (unsigned int)i, reg.start, reg.end);
			return false;
		}
	}
	ndks_boot.bi_frame->untyped =
		(seL4_SlotRegion){.start = first_untyped_slot, .end = ndks_boot.slot_pos_cur};
	return true;
}
void bi_finalise(void)
{
	ndks_boot.bi_frame->empty =
		(seL4_SlotRegion){.start = ndks_boot.slot_pos_cur, .end = (1ul << (13))};
}
static inline pptr_t ceiling_kernel_window(pptr_t p)
{
	/* Adjust address if it exceeds the kernel window
	 * Note that we compare physical address in case of overflow.
	 */
	if (addrFromPPtr((void *)p) > (PPTR_TOP - (PPTR_BASE - 0x0ul))) {
		p = PPTR_TOP;
	}
	return p;
}
static bool_t check_available_memory(word_t n_available, const p_region_t *available)
{
	/* The system configuration is broken if no region is available. */
	if (0 == n_available) {
		printf("ERROR: no memory regions available\n");
		return false;
	}
	printf("available phys memory regions: %lu \n", n_available);
	/* Force ordering and exclusivity of available regions. */
	for (word_t i = 0; i < n_available; i++) {
		const p_region_t *r = &available[i];
		printf("  [%lx..%lx]\n", r->start, r->end);
		/* Available regions must be sane */
		if (r->start > r->end) {
			printf("ERROR: memory region %lu has start > end\n", i);
			return false;
		}
		/* Available regions can't be empty. */
		if (r->start == r->end) {
			printf("ERROR: memory region %lu empty\n", i);
			return false;
		}
		/* Regions must be ordered and must not overlap. */
		if ((i > 0) && (r->start < available[i - 1].end)) {
			printf("ERROR: memory region %d in wrong order\n", (int)i);
			return false;
		}
	}
	return true;
}
static bool_t check_reserved_memory(word_t n_reserved, const region_t *reserved)
{
	printf("reserved virt address space regions: %"
	       "lu"
	       "\n",
	       n_reserved);
	/* Force ordering and exclusivity of reserved regions. */
	for (word_t i = 0; i < n_reserved; i++) {
		const region_t *r = &reserved[i];
		printf("  [%"
		       "lx"
		       "..%"
		       "lx"
		       "]\n",
		       r->start, r->end);
		/* Reserved regions must be sane, the size is allowed to be zero. */
		if (r->start > r->end) {
			printf("ERROR: reserved region %"
			       "lu"
			       " has start > end\n",
			       i);
			return false;
		}
		/* Regions must be ordered and must not overlap. */
		if ((i > 0) && (r->start < reserved[i - 1].end)) {
			printf("ERROR: reserved region %"
			       "lu"
			       " in wrong order\n",
			       i);
			return false;
		}
	}
	return true;
}
/* we can't declare arrays on the stack, so this is space for
 * the function below to use. */
static region_t avail_reg[((sizeof(avail_p_regs) / sizeof((avail_p_regs)[0])) + 0 + 1 + 1)];
/**
 * Dynamically initialise the available memory on the platform.
 * A region represents an area of memory.
 */
bool_t init_freemem(word_t n_available, const p_region_t *available, word_t n_reserved,
		    const region_t *reserved, v_region_t it_v_reg, word_t extra_bi_size_bits)
{
	if (!check_available_memory(n_available, available)) {
		return false;
	}
	if (!check_reserved_memory(n_reserved, reserved)) {
		return false;
	}
	for (word_t i = 0; i < (sizeof(ndks_boot.freemem) / sizeof((ndks_boot.freemem)[0])); i++) {
		ndks_boot.freemem[i] = (region_t){.start = 0, .end = 0};
	}
	/* convert the available regions to pptrs */
	for (word_t i = 0; i < n_available; i++) {
		avail_reg[i] = paddr_to_pptr_reg(available[i]);
		avail_reg[i].end = ceiling_kernel_window(avail_reg[i].end);
		avail_reg[i].start = ceiling_kernel_window(avail_reg[i].start);
	}
	word_t a = 0;
	word_t r = 0;
	/* Now iterate through the available regions, removing any reserved regions. */
	while (a < n_available && r < n_reserved) {
		if (reserved[r].start == reserved[r].end) {
			/* reserved region is empty - skip it */
			r++;
		} else if (avail_reg[a].start >= avail_reg[a].end) {
			/* skip the entire region - it's empty now after trimming */
			a++;
		} else if (reserved[r].end <= avail_reg[a].start) {
			/* the reserved region is below the available region - skip it */
			reserve_region(pptr_to_paddr_reg(reserved[r]));
			r++;
		} else if (reserved[r].start >= avail_reg[a].end) {
			/* the reserved region is above the available region - take the whole thing
			 */
			insert_region(avail_reg[a]);
			a++;
		} else {
			/* the reserved region overlaps with the available region */
			if (reserved[r].start <= avail_reg[a].start) {
				/* the region overlaps with the start of the available region.
				 * trim start of the available region */
				avail_reg[a].start = (((avail_reg[a].end) < (reserved[r].end))
							      ? (avail_reg[a].end)
							      : (reserved[r].end));
				reserve_region(pptr_to_paddr_reg(reserved[r]));
				r++;
			} else {
				/* take the first chunk of the available region and move
				 * the start to the end of the reserved region */
				region_t m = avail_reg[a];
				m.end = reserved[r].start;
				insert_region(m);
				if (avail_reg[a].end > reserved[r].end) {
					avail_reg[a].start = reserved[r].end;
					reserve_region(pptr_to_paddr_reg(reserved[r]));
					r++;
				} else {
					a++;
				}
			}
		}
	}
	for (; r < n_reserved; r++) {
		if (reserved[r].start < reserved[r].end) {
			reserve_region(pptr_to_paddr_reg(reserved[r]));
		}
	}
	/* no more reserved regions - add the rest */
	for (; a < n_available; a++) {
		if (avail_reg[a].start < avail_reg[a].end) {
			insert_region(avail_reg[a]);
		}
	}
	/* now try to fit the root server objects into a region */
	int i = (sizeof(ndks_boot.freemem) / sizeof((ndks_boot.freemem)[0])) - 1;
	if (!is_reg_empty(ndks_boot.freemem[i])) {
		printf("ERROR: insufficient MAX_NUM_FREEMEM_REG (%u)\n",
		       (unsigned int)((sizeof(avail_p_regs) / sizeof((avail_p_regs)[0])) + 0 + 1 +
				      1));
		return false;
	}
	/* skip any empty regions */
	for (; i >= 0 && is_reg_empty(ndks_boot.freemem[i]); i--)
		;
	/* try to grab the last available p region to create the root server objects
	 * from. If possible, retain any left over memory as an extra p region */
	word_t size = calculate_rootserver_size(it_v_reg, extra_bi_size_bits);
	word_t max = rootserver_max_size_bits(extra_bi_size_bits);
	for (; i >= 0; i--) {
		/* Invariant: both i and (i + 1) are valid indices in ndks_boot.freemem. */
		/* Invariant; the region at index i is the current candidate.
		 * Invariant: regions 0 up to (i - 1), if any, are additional candidates.
		 * Invariant: region (i + 1) is empty. */
		/* Invariant: regions above (i + 1), if any, are empty or too small to use.
		 * Invariant: all non-empty regions are ordered, disjoint and unallocated. */
		/* We make a fresh variable to index the known-empty region, because the
		 * SimplExportAndRefine verification test has poor support for array
		 * indices that are sums of variables and small constants. */
		int empty_index = i + 1;
		/* Try to take the top-most suitably sized and aligned chunk. */
		pptr_t unaligned_start = ndks_boot.freemem[i].end - size;
		pptr_t start = (((unaligned_start) >> (max)) << (max));
		/* if unaligned_start didn't underflow, and start fits in the region,
		 * then we've found a region that fits the root server objects. */
		if (unaligned_start <= ndks_boot.freemem[i].end &&
		    start >= ndks_boot.freemem[i].start) {
			create_rootserver_objects(start, it_v_reg, extra_bi_size_bits);
			/* There may be leftovers before and after the memory we used. */
			/* Shuffle the after leftover up to the empty slot (i + 1). */
			ndks_boot.freemem[empty_index] =
				(region_t){.start = start + size, .end = ndks_boot.freemem[i].end};
			/* Leave the before leftover in current slot i. */
			ndks_boot.freemem[i].end = start;
			/* Regions i and (i + 1) are now well defined, ordered, disjoint,
			 * and unallocated, so we can return successfully. */
			return true;
		}
		/* Region i isn't big enough, so shuffle it up to slot (i + 1),
		 * which we know is unused. */
		ndks_boot.freemem[empty_index] = ndks_boot.freemem[i];
		/* Now region i is unused, so make it empty to reestablish the invariant
		 * for the next iteration (when it will be slot i + 1). */
		ndks_boot.freemem[i] = (region_t){.start = 0, .end = 0};
	}
	/* We didn't find a big enough region. */
	printf("ERROR: no free memory region is big enough for root server "
	       "objects, need size/alignment of 2^%"
	       "lu"
	       "\n",
	       max);
	return false;
}
lookupCap_ret_t lookupCap(tcb_t *thread, cptr_t cPtr)
{
	lookupSlot_raw_ret_t lu_ret;
	lookupCap_ret_t ret;
	lu_ret = lookupSlot(thread, cPtr);
	if (__builtin_expect(!!(lu_ret.status != EXCEPTION_NONE), 0)) {
		ret.status = lu_ret.status;
		ret.cap = cap_null_cap_new();
		return ret;
	}
	ret.status = EXCEPTION_NONE;
	ret.cap = lu_ret.slot->cap;
	return ret;
}
lookupCapAndSlot_ret_t lookupCapAndSlot(tcb_t *thread, cptr_t cPtr)
{
	lookupSlot_raw_ret_t lu_ret;
	lookupCapAndSlot_ret_t ret;
	lu_ret = lookupSlot(thread, cPtr);
	if (__builtin_expect(!!(lu_ret.status != EXCEPTION_NONE), 0)) {
		ret.status = lu_ret.status;
		ret.slot = NULL;
		ret.cap = cap_null_cap_new();
		return ret;
	}
	ret.status = EXCEPTION_NONE;
	ret.slot = lu_ret.slot;
	ret.cap = lu_ret.slot->cap;
	return ret;
}
lookupSlot_raw_ret_t lookupSlot(tcb_t *thread, cptr_t capptr)
{
	cap_t threadRoot;
	resolveAddressBits_ret_t res_ret;
	lookupSlot_raw_ret_t ret;
	threadRoot = (((cte_t *)((word_t)(thread) & ~((1ul << (11)) - 1ul))) + (tcbCTable))->cap;
	res_ret = resolveAddressBits(threadRoot, capptr, (1 << 6));
	ret.status = res_ret.status;
	ret.slot = res_ret.slot;
	return ret;
}
lookupSlot_ret_t lookupSlotForCNodeOp(bool_t isSource, cap_t root, cptr_t capptr, word_t depth)
{
	resolveAddressBits_ret_t res_ret;
	lookupSlot_ret_t ret;
	ret.slot = NULL;
	if (__builtin_expect(!!(cap_get_capType(root) != cap_cnode_cap), 0)) {
		current_syscall_error.type = seL4_FailedLookup;
		current_syscall_error.failedLookupWasSource = isSource;
		current_lookup_fault = lookup_fault_invalid_root_new();
		ret.status = EXCEPTION_SYSCALL_ERROR;
		return ret;
	}
	if (__builtin_expect(!!(depth < 1 || depth > (1 << 6)), 0)) {
		current_syscall_error.type = seL4_RangeError;
		current_syscall_error.rangeErrorMin = 1;
		current_syscall_error.rangeErrorMax = (1 << 6);
		ret.status = EXCEPTION_SYSCALL_ERROR;
		return ret;
	}
	res_ret = resolveAddressBits(root, capptr, depth);
	if (__builtin_expect(!!(res_ret.status != EXCEPTION_NONE), 0)) {
		current_syscall_error.type = seL4_FailedLookup;
		current_syscall_error.failedLookupWasSource = isSource;
		/* current_lookup_fault will have been set by resolveAddressBits */
		ret.status = EXCEPTION_SYSCALL_ERROR;
		return ret;
	}
	if (__builtin_expect(!!(res_ret.bitsRemaining != 0), 0)) {
		current_syscall_error.type = seL4_FailedLookup;
		current_syscall_error.failedLookupWasSource = isSource;
		current_lookup_fault = lookup_fault_depth_mismatch_new(0, res_ret.bitsRemaining);
		ret.status = EXCEPTION_SYSCALL_ERROR;
		return ret;
	}
	ret.slot = res_ret.slot;
	ret.status = EXCEPTION_NONE;
	return ret;
}
lookupSlot_ret_t lookupSourceSlot(cap_t root, cptr_t capptr, word_t depth)
{
	return lookupSlotForCNodeOp(true, root, capptr, depth);
}
lookupSlot_ret_t lookupTargetSlot(cap_t root, cptr_t capptr, word_t depth)
{
	return lookupSlotForCNodeOp(false, root, capptr, depth);
}
lookupSlot_ret_t lookupPivotSlot(cap_t root, cptr_t capptr, word_t depth)
{
	return lookupSlotForCNodeOp(true, root, capptr, depth);
}
resolveAddressBits_ret_t resolveAddressBits(cap_t nodeCap, cptr_t capptr, word_t n_bits)
{
	resolveAddressBits_ret_t ret;
	word_t radixBits, guardBits, levelBits, guard;
	word_t capGuard, offset;
	cte_t *slot;
	ret.bitsRemaining = n_bits;
	ret.slot = NULL;
	if (cap_get_capType(nodeCap) != cap_cnode_cap) {
		current_lookup_fault = lookup_fault_invalid_root_new();
		ret.status = EXCEPTION_LOOKUP_FAULT;
		return ret;
	}
	while (1) {
		radixBits = cap_cnode_cap_get_capCNodeRadix(nodeCap);
		guardBits = cap_cnode_cap_get_capCNodeGuardSize(nodeCap);
		levelBits = radixBits + guardBits;
		/* Haskell error: "All CNodes must resolve bits" */
		capGuard = cap_cnode_cap_get_capCNodeGuard(nodeCap);
		/* The MASK(wordRadix) here is to avoid the case where
		 * n_bits = wordBits (=2^wordRadix) and guardBits = 0, as it violates
		 * the C spec to shift right by more than wordBits-1.
		 */
		guard = (capptr >> ((n_bits - guardBits) & ((1ul << (6)) - 1ul))) &
			((1ul << (guardBits)) - 1ul);
		if (guardBits > n_bits || guard != capGuard) {
			current_lookup_fault =
				lookup_fault_guard_mismatch_new(capGuard, n_bits, guardBits);
			ret.status = EXCEPTION_LOOKUP_FAULT;
			return ret;
		}
		if (levelBits > n_bits) {
			current_lookup_fault = lookup_fault_depth_mismatch_new(levelBits, n_bits);
			ret.status = EXCEPTION_LOOKUP_FAULT;
			return ret;
		}
		offset = (capptr >> (n_bits - levelBits)) & ((1ul << (radixBits)) - 1ul);
		slot = ((cte_t *)(cap_cnode_cap_get_capCNodePtr(nodeCap))) + offset;
		if (n_bits == levelBits) {
			ret.status = EXCEPTION_NONE;
			ret.slot = slot;
			ret.bitsRemaining = 0;
			return ret;
		}
		/** GHOSTUPD: "(\<acute>levelBits > 0, id)" */
		n_bits -= levelBits;
		nodeCap = slot->cap;
		if (cap_get_capType(nodeCap) != cap_cnode_cap) {
			ret.status = EXCEPTION_NONE;
			ret.slot = slot;
			ret.bitsRemaining = n_bits;
			return ret;
		}
	}
	__builtin_unreachable();
}
void handleFault(tcb_t *tptr)
{
	exception_t status;
	seL4_Fault_t fault = current_fault;
	status = sendFaultIPC(tptr);
	if (status != EXCEPTION_NONE) {
		handleDoubleFault(tptr, fault);
	}
}
exception_t sendFaultIPC(tcb_t *tptr)
{
	cptr_t handlerCPtr;
	cap_t handlerCap;
	lookupCap_ret_t lu_ret;
	lookup_fault_t original_lookup_fault;
	original_lookup_fault = current_lookup_fault;
	handlerCPtr = tptr->tcbFaultHandler;
	lu_ret = lookupCap(tptr, handlerCPtr);
	if (lu_ret.status != EXCEPTION_NONE) {
		current_fault = seL4_Fault_CapFault_new(handlerCPtr, false);
		return EXCEPTION_FAULT;
	}
	handlerCap = lu_ret.cap;
	if (cap_get_capType(handlerCap) == cap_endpoint_cap &&
	    cap_endpoint_cap_get_capCanSend(handlerCap) &&
	    (cap_endpoint_cap_get_capCanGrant(handlerCap) ||
	     cap_endpoint_cap_get_capCanGrantReply(handlerCap))) {
		tptr->tcbFault = current_fault;
		if (seL4_Fault_get_seL4_FaultType(current_fault) == seL4_Fault_CapFault) {
			tptr->tcbLookupFailure = original_lookup_fault;
		}
		sendIPC(true, true, cap_endpoint_cap_get_capEPBadge(handlerCap),
			cap_endpoint_cap_get_capCanGrant(handlerCap), true, tptr,
			((endpoint_t *)(cap_endpoint_cap_get_capEPPtr(handlerCap))));
		return EXCEPTION_NONE;
	} else {
		current_fault = seL4_Fault_CapFault_new(handlerCPtr, false);
		current_lookup_fault = lookup_fault_missing_capability_new(0);
		return EXCEPTION_FAULT;
	}
}
static void print_fault(seL4_Fault_t f)
{
	switch (seL4_Fault_get_seL4_FaultType(f)) {
	case seL4_Fault_NullFault:
		printf("null fault");
		break;
	case seL4_Fault_CapFault:
		printf("cap fault in %s phase at address %p",
		       seL4_Fault_CapFault_get_inReceivePhase(f) ? "receive" : "send",
		       (void *)seL4_Fault_CapFault_get_address(f));
		break;
	case seL4_Fault_VMFault:
		printf("vm fault on %s at address %p with status %p",
		       seL4_Fault_VMFault_get_instructionFault(f) ? "code" : "data",
		       (void *)seL4_Fault_VMFault_get_address(f),
		       (void *)seL4_Fault_VMFault_get_FSR(f));
		break;
	case seL4_Fault_UnknownSyscall:
		printf("unknown syscall %p",
		       (void *)seL4_Fault_UnknownSyscall_get_syscallNumber(f));
		break;
	case seL4_Fault_UserException:
		printf("user exception %p code %p", (void *)seL4_Fault_UserException_get_number(f),
		       (void *)seL4_Fault_UserException_get_code(f));
		break;
	default:
		printf("unknown fault");
		break;
	}
}
/* The second fault, ex2, is stored in the global current_fault */
void handleDoubleFault(tcb_t *tptr, seL4_Fault_t ex1)
{
	seL4_Fault_t ex2 = current_fault;
	printf("Caught ");
	print_fault(ex2);
	printf("\nwhile trying to handle:\n");
	print_fault(ex1);
	printf("\nin thread %p \"%s\" ", tptr,
	       ((debug_tcb_t *)(((cte_t *)((word_t)(tptr) & ~((1ul << (11)) - 1ul))) +
				(tcbCNodeEntries)))
		       ->tcbName);
	printf("at address %p\n", (void *)getRestartPC(tptr));
	printf("With stack:\n");
	Arch_userStackTrace(tptr);
	setThreadState(tptr, ThreadState_Inactive);
}
__attribute__((__aligned__(4096))) char kernel_stack_alloc[1][(1ul << (12))];
static seL4_MessageInfo_t transferCaps(seL4_MessageInfo_t info, endpoint_t *endpoint,
				       tcb_t *receiver, word_t *receiveBuffer);
void configureIdleThread(tcb_t *tcb)
{
	Arch_configureIdleThread(tcb);
	setThreadState(tcb, ThreadState_IdleThreadState);
}
void activateThread(void)
{
	switch (thread_state_get_tsType(ksCurThread->tcbState)) {
	case ThreadState_Running:
		break;
	case ThreadState_Restart: {
		word_t pc;
		pc = getRestartPC(ksCurThread);
		setNextPC(ksCurThread, pc);
		setThreadState(ksCurThread, ThreadState_Running);
		break;
	}
	case ThreadState_IdleThreadState:
		Arch_activateIdleThread(ksCurThread);
		break;
	default:
		_fail("Current thread is blocked",
		      "/home/lab/projects/seL4/seL4test/kernel/src/kernel/thread.c", 65, __func__);
	}
}
void suspend(tcb_t *target)
{
	cancelIPC(target);
	if (thread_state_get_tsType(target->tcbState) == ThreadState_Running) {
		/* whilst in the running state it is possible that restart pc of a thread is
		 * incorrect. As we do not know what state this thread will transition to
		 * after we make it inactive we update its restart pc so that the thread next
		 * runs at the correct address whether it is restarted or moved directly to
		 * running */
		updateRestartPC(target);
	}
	setThreadState(target, ThreadState_Inactive);
	tcbSchedDequeue(target);
}
void restart(tcb_t *target)
{
	if (isStopped(target)) {
		cancelIPC(target);
		setupReplyMaster(target);
		setThreadState(target, ThreadState_Restart);
		tcbSchedEnqueue(target);
		possibleSwitchTo(target);
	}
}
void doIPCTransfer(tcb_t *sender, endpoint_t *endpoint, word_t badge, bool_t grant, tcb_t *receiver)
{
	void *receiveBuffer, *sendBuffer;
	receiveBuffer = lookupIPCBuffer(true, receiver);
	if (seL4_Fault_get_seL4_FaultType(sender->tcbFault) == seL4_Fault_NullFault) {
		sendBuffer = lookupIPCBuffer(false, sender);
		doNormalTransfer(sender, sendBuffer, endpoint, badge, grant, receiver,
				 receiveBuffer);
	} else {
		doFaultTransfer(badge, sender, receiver, receiveBuffer);
	}
}
void doReplyTransfer(tcb_t *sender, tcb_t *receiver, cte_t *slot, bool_t grant)
{
	word_t fault_type = seL4_Fault_get_seL4_FaultType(receiver->tcbFault);
	if (fault_type == seL4_Fault_NullFault) {
		doIPCTransfer(sender, NULL, 0, grant, receiver);
		/** GHOSTUPD: "(True, gs_set_assn cteDeleteOne_'proc (ucast cap_reply_cap))" */
		cteDeleteOne(slot);
		setThreadState(receiver, ThreadState_Running);
		possibleSwitchTo(receiver);
	} else {
		/** GHOSTUPD: "(True, gs_set_assn cteDeleteOne_'proc (ucast cap_reply_cap))" */
		cteDeleteOne(slot);
		bool_t restart = handleFaultReply(receiver, sender);
		receiver->tcbFault = seL4_Fault_NullFault_new();
		if (restart) {
			setThreadState(receiver, ThreadState_Restart);
			possibleSwitchTo(receiver);
		} else {
			setThreadState(receiver, ThreadState_Inactive);
		}
	}
}
void doNormalTransfer(tcb_t *sender, word_t *sendBuffer, endpoint_t *endpoint, word_t badge,
		      bool_t canGrant, tcb_t *receiver, word_t *receiveBuffer)
{
	word_t msgTransferred;
	seL4_MessageInfo_t tag;
	exception_t status;
	tag = messageInfoFromWord(getRegister(sender, msgInfoRegister));
	if (canGrant) {
		status = lookupExtraCaps(sender, sendBuffer, tag);
		if (status != EXCEPTION_NONE) {
			current_extra_caps.excaprefs[0] = NULL;
		}
	} else {
		current_extra_caps.excaprefs[0] = NULL;
	}
	msgTransferred = copyMRs(sender, sendBuffer, receiver, receiveBuffer,
				 seL4_MessageInfo_get_length(tag));
	tag = transferCaps(tag, endpoint, receiver, receiveBuffer);
	tag = seL4_MessageInfo_set_length(tag, msgTransferred);
	setRegister(receiver, msgInfoRegister, wordFromMessageInfo(tag));
	setRegister(receiver, badgeRegister, badge);
}
void doFaultTransfer(word_t badge, tcb_t *sender, tcb_t *receiver, word_t *receiverIPCBuffer)
{
	word_t sent;
	seL4_MessageInfo_t msgInfo;
	sent = setMRs_fault(sender, receiver, receiverIPCBuffer);
	msgInfo = seL4_MessageInfo_new(seL4_Fault_get_seL4_FaultType(sender->tcbFault), 0, 0, sent);
	setRegister(receiver, msgInfoRegister, wordFromMessageInfo(msgInfo));
	setRegister(receiver, badgeRegister, badge);
}
/* Like getReceiveSlots, this is specialised for single-cap transfer. */
static seL4_MessageInfo_t transferCaps(seL4_MessageInfo_t info, endpoint_t *endpoint,
				       tcb_t *receiver, word_t *receiveBuffer)
{
	word_t i;
	cte_t *destSlot;
	info = seL4_MessageInfo_set_extraCaps(info, 0);
	info = seL4_MessageInfo_set_capsUnwrapped(info, 0);
	if (!current_extra_caps.excaprefs[0] || !receiveBuffer) {
		return info;
	}
	destSlot = getReceiveSlots(receiver, receiveBuffer);
	for (i = 0;
	     i < ((1ul << (seL4_MsgExtraCapBits)) - 1) && current_extra_caps.excaprefs[i] != NULL;
	     i++) {
		cte_t *slot = current_extra_caps.excaprefs[i];
		cap_t cap = slot->cap;
		if (cap_get_capType(cap) == cap_endpoint_cap &&
		    ((endpoint_t *)(cap_endpoint_cap_get_capEPPtr(cap))) == endpoint) {
			/* If this is a cap to the endpoint on which the message was sent,
			 * only transfer the badge, not the cap. */
			setExtraBadge(receiveBuffer, cap_endpoint_cap_get_capEPBadge(cap), i);
			info = seL4_MessageInfo_set_capsUnwrapped(
				info, seL4_MessageInfo_get_capsUnwrapped(info) | (1 << i));
		} else {
			deriveCap_ret_t dc_ret;
			if (!destSlot) {
				break;
			}
			dc_ret = deriveCap(slot, cap);
			if (dc_ret.status != EXCEPTION_NONE) {
				break;
			}
			if (cap_get_capType(dc_ret.cap) == cap_null_cap) {
				break;
			}
			cteInsert(dc_ret.cap, slot, destSlot);
			destSlot = NULL;
		}
	}
	return seL4_MessageInfo_set_extraCaps(info, i);
}
void doNBRecvFailedTransfer(tcb_t *thread)
{
	/* Set the badge register to 0 to indicate there was no message */
	setRegister(thread, badgeRegister, 0);
}
static void nextDomain(void)
{
	ksDomScheduleIdx++;
	if (ksDomScheduleIdx >= ksDomScheduleLength) {
		ksDomScheduleIdx = 0;
	}
	ksWorkUnitsCompleted = 0;
	ksCurDomain = ksDomSchedule[ksDomScheduleIdx].domain;
	ksDomainTime = ksDomSchedule[ksDomScheduleIdx].length;
}
static void scheduleChooseNewThread(void)
{
	if (ksDomainTime == 0) {
		nextDomain();
	}
	chooseThread();
}
void schedule(void)
{
	if (ksSchedulerAction != ((tcb_t *)0)) {
		bool_t was_runnable;
		if (isRunnable(ksCurThread)) {
			was_runnable = true;
			tcbSchedEnqueue(ksCurThread);
		} else {
			was_runnable = false;
		}
		if (ksSchedulerAction == ((tcb_t *)1)) {
			scheduleChooseNewThread();
		} else {
			tcb_t *candidate = ksSchedulerAction;
			/* Avoid checking bitmap when ksCurThread is higher prio, to
			 * match fast path.
			 * Don't look at ksCurThread prio when it's idle, to respect
			 * information flow in non-fastpath cases. */
			bool_t fastfail = ksCurThread == ksIdleThread ||
					  (candidate->tcbPriority < ksCurThread->tcbPriority);
			if (fastfail && !isHighestPrio(ksCurDomain, candidate->tcbPriority)) {
				tcbSchedEnqueue(candidate);
				/* we can't, need to reschedule */
				ksSchedulerAction = ((tcb_t *)1);
				scheduleChooseNewThread();
			} else if (was_runnable &&
				   candidate->tcbPriority == ksCurThread->tcbPriority) {
				/* We append the candidate at the end of the scheduling queue, that
				 * way the current thread, that was enqueued at the start of the
				 * scheduling queue will get picked during chooseNewThread */
				tcbSchedAppend(candidate);
				ksSchedulerAction = ((tcb_t *)1);
				scheduleChooseNewThread();
			} else {
				switchToThread(candidate);
			}
		}
	}
	ksSchedulerAction = ((tcb_t *)0);
}
void chooseThread(void)
{
	word_t prio;
	word_t dom;
	tcb_t *thread;
	if (numDomains > 1) {
		dom = ksCurDomain;
	} else {
		dom = 0;
	}
	if (__builtin_expect(!!(ksReadyQueuesL1Bitmap[dom]), 1)) {
		prio = getHighestPrio(dom);
		thread = ksReadyQueues[ready_queues_index(dom, prio)].head;
		switchToThread(thread);
	} else {
		switchToIdleThread();
	}
}
void switchToThread(tcb_t *thread)
{
	Arch_switchToThread(thread);
	tcbSchedDequeue(thread);
	ksCurThread = thread;
}
void switchToIdleThread(void)
{
	Arch_switchToIdleThread();
	ksCurThread = ksIdleThread;
}
void setDomain(tcb_t *tptr, dom_t dom)
{
	tcbSchedDequeue(tptr);
	tptr->tcbDomain = dom;
	if (isRunnable(tptr)) {
		tcbSchedEnqueue(tptr);
	}
	if (tptr == ksCurThread) {
		rescheduleRequired();
	}
}
void setMCPriority(tcb_t *tptr, prio_t mcp)
{
	tptr->tcbMCP = mcp;
}
void setPriority(tcb_t *tptr, prio_t prio)
{
	tcbSchedDequeue(tptr);
	tptr->tcbPriority = prio;
	if (isRunnable(tptr)) {
		if (tptr == ksCurThread) {
			rescheduleRequired();
		} else {
			possibleSwitchTo(tptr);
		}
	}
}
/* Note that this thread will possibly continue at the end of this kernel
 * entry. Do not queue it yet, since a queue+unqueue operation is wasteful
 * if it will be picked. Instead, it waits in the 'ksSchedulerAction' site
 * on which the scheduler will take action. */
void possibleSwitchTo(tcb_t *target)
{
	if (ksCurDomain != target->tcbDomain) {
		tcbSchedEnqueue(target);
	} else if (ksSchedulerAction != ((tcb_t *)0)) {
		/* Too many threads want special treatment, use regular queues. */
		rescheduleRequired();
		tcbSchedEnqueue(target);
	} else {
		ksSchedulerAction = target;
	}
}
void setThreadState(tcb_t *tptr, _thread_state_t ts)
{
	thread_state_ptr_set_tsType(&tptr->tcbState, ts);
	scheduleTCB(tptr);
}
void scheduleTCB(tcb_t *tptr)
{
	if (tptr == ksCurThread && ksSchedulerAction == ((tcb_t *)0) && !isRunnable(tptr)) {
		rescheduleRequired();
	}
}
void timerTick(void)
{
	if (__builtin_expect(
		    !!(thread_state_get_tsType(ksCurThread->tcbState) == ThreadState_Running), 1)) {
		if (ksCurThread->tcbTimeSlice > 1) {
			ksCurThread->tcbTimeSlice--;
		} else {
			ksCurThread->tcbTimeSlice = 5;
			tcbSchedAppend(ksCurThread);
			rescheduleRequired();
		}
	}
	if (numDomains > 1) {
		ksDomainTime--;
		if (ksDomainTime == 0) {
			rescheduleRequired();
		}
	}
}
void rescheduleRequired(void)
{
	if (ksSchedulerAction != ((tcb_t *)0) && ksSchedulerAction != ((tcb_t *)1)) {
		tcbSchedEnqueue(ksSchedulerAction);
	}
	ksSchedulerAction = ((tcb_t *)1);
}
static inline void resetTimer(void);
/* seen list - check this array before we print cnode and vspace */
/* TBD: This is to avoid traversing the same cnode. It should be applied to object
 * as well since the extractor might comes across multiple caps to the same object.
 */
cap_t seen_list[256];
int watermark = 0;
void add_to_seen(cap_t c)
{
	/* Won't work well if there're more than SEEN_SZ cnode */
	if (watermark <= 256) {
		seen_list[watermark] = c;
		watermark++;
	}
}
void reset_seen_list(void)
{
	memset(seen_list, 0, 256 * sizeof(seen_list[0]));
	watermark = 0;
}
bool_t seen(cap_t c)
{
	for (int i = 0; i < watermark; i++) {
		if (same_cap(seen_list[i], c)) {
			return true;
		}
	}
	return false;
}
bool_t same_cap(cap_t a, cap_t b)
{
	return (a.words[0] == b.words[0] && a.words[1] == b.words[1]);
}
/* Return true if strings are the same */
static inline bool_t strings_equal(const char *str1, const char *str2)
{
	while (*str1 && *str2 && (*str1 == *str2)) {
		str1++;
		str2++;
	}
	return !(*(const unsigned char *)str1 - *(const unsigned char *)str2);
}
/* Return true if the tcb is for rootserver or idle thread */
bool_t root_or_idle_tcb(tcb_t *tcb)
{
	return (strings_equal(((debug_tcb_t *)(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) +
					       (tcbCNodeEntries)))
				      ->tcbName,
			      "rootserver") ||
		strings_equal(((debug_tcb_t *)(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) +
					       (tcbCNodeEntries)))
				      ->tcbName,
			      "idle_thread"));
}
/*
 * Print objects
 */
void obj_tcb_print_attrs(tcb_t *tcb)
{
	printf("(addr: 0x%lx, ip: 0x%lx, sp: 0x%lx, prio: %lu, max_prio: %lu",
	       (long unsigned int)tcb->tcbIPCBuffer, (long unsigned int)getRestartPC(tcb),
	       (long unsigned int)get_tcb_sp(tcb), (long unsigned int)tcb->tcbPriority,
	       (long unsigned int)tcb->tcbMCP);
	/* init */
	printf(", dom: %ld)\n", tcb->tcbDomain);
}
void obj_ut_print_attrs(cte_t *slot, tcb_t *tcb)
{
	/* might have two untypeds with the same address but different size */
	printf("%p_%lu_untyped = ut (%lu bits, paddr: %p) {",
	       (void *)cap_untyped_cap_get_capPtr(slot->cap),
	       (long unsigned int)cap_untyped_cap_get_capBlockSize(slot->cap),
	       (long unsigned int)cap_untyped_cap_get_capBlockSize(slot->cap),
	       ((word_t *)(cap_untyped_cap_get_capPtr(slot->cap))));
	/* there is no need to check for a NullCap as NullCaps are
	always accompanied by null mdb pointers */
	for (cte_t *nextPtr = ((cte_t *)(mdb_node_get_mdbNext(slot->cteMDBNode)));
	     nextPtr && isMDBParentOf(slot, nextPtr);
	     nextPtr = ((cte_t *)(mdb_node_get_mdbNext(slot->cteMDBNode)))) {
		if (!sameRegionAs(slot->cap, nextPtr->cap)) {
			/* TBD:
			 * - this will print out the attributes of the cap, which it shouldn't
			 *
			 * - might be a pathological case where an untyped has a child cap that
			 *   isn't reachable from any of the non root threads. This would result
			 *   in an object being mentioned but never properly defined
			 */
			print_cap(nextPtr->cap);
		}
	}
	printf("}\n");
}
void obj_cnode_print_attrs(cap_t cnode)
{
	printf("(%lu bits)\n", (long unsigned int)cap_cnode_cap_get_capCNodeRadix(cnode));
}
void obj_tcb_print_cnodes(cap_t cnode, tcb_t *tcb)
{
	if (seen(cnode)) {
		return;
	}
	add_to_seen(cnode);
	printf("%p_cnode = cnode ", (void *)cap_cnode_cap_get_capCNodePtr(cnode));
	obj_cnode_print_attrs(cnode);
	word_t radix = cap_cnode_cap_get_capCNodeRadix(cnode);
	for (uint32_t i = 0; i < (1 << radix); i++) {
		lookupCapAndSlot_ret_t c = lookupCapAndSlot(tcb, i);
		if (cap_get_capType(c.cap) == cap_untyped_cap) {
			/* we need `cte_t *` to print out the slots of an untyped object */
			obj_ut_print_attrs(c.slot, tcb);
		} else if (cap_get_capType(c.cap) == cap_cnode_cap) {
			/* TBD: deal with nested cnodes */
		} else if (cap_get_capType(c.cap) != cap_null_cap) {
			print_object(c.cap);
		}
	}
}
/*
 * Caps
 */
void cap_cnode_print_attrs(cap_t cnode)
{
	printf("(guard: %lu, guard_size: %lu)\n",
	       (long unsigned int)cap_cnode_cap_get_capCNodeGuard(cnode),
	       (long unsigned int)cap_cnode_cap_get_capCNodeGuardSize(cnode));
}
void cap_ep_print_attrs(cap_t ep)
{
	printf("(");
	cap_endpoint_cap_get_capCanReceive(ep) ? putchar('R') : 0;
	cap_endpoint_cap_get_capCanSend(ep) ? putchar('W') : 0;
	cap_endpoint_cap_get_capCanGrant(ep) ? putchar('G') : 0;
	cap_endpoint_cap_get_capCanGrantReply(ep) ? putchar('P') : 0;
	long unsigned int badge = cap_endpoint_cap_get_capEPBadge(ep);
	badge ? printf(", badge: %lu)\n", badge) : printf(")\n");
}
void cap_ntfn_print_attrs(cap_t ntfn)
{
	printf("(");
	cap_notification_cap_get_capNtfnCanReceive(ntfn) ? putchar('R') : 0;
	cap_notification_cap_get_capNtfnCanSend(ntfn) ? putchar('W') : 0;
	long unsigned int badge = cap_notification_cap_get_capNtfnBadge(ntfn);
	badge ? printf(", badge: %lu)\n", badge) : printf(")\n");
}
/*
 * print object slots
 */
void obj_tcb_print_slots(tcb_t *tcb)
{
	printf("%p_tcb {\n", tcb);
	/* CSpace root */
	if (cap_get_capType(
		    (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbCTable))->cap) !=
	    cap_null_cap) {
		printf("cspace: %p_cnode ",
		       (void *)cap_cnode_cap_get_capCNodePtr(
			       (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbCTable))
				       ->cap));
		cap_cnode_print_attrs(
			(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbCTable))->cap);
	}
	/* VSpace root */
	if (cap_get_capType(
		    (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))->cap) !=
	    cap_null_cap) {
		printf("vspace: %p_pd\n",
		       ((pgde_t *)(cap_page_global_directory_cap_get_capPGDBasePtr(
			       (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbVTable))
				       ->cap))));
	}
	/* IPC buffer cap slot */
	if (cap_get_capType(
		    (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbBuffer))->cap) !=
	    cap_null_cap) {
		/* TBD: print out the bound vcpu */
		print_ipc_buffer_slot(tcb);
	}
	/* Reply cap slot */
	if (cap_get_capType(
		    (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbReply))->cap) !=
	    cap_null_cap) {
		printf("reply_slot: %p_reply\n",
		       (void *)cap_reply_cap_get_capTCBPtr(
			       (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbReply))
				       ->cap));
	}
	/* TCB of most recent IPC sender */
	if (cap_get_capType(
		    (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbCaller))->cap) !=
	    cap_null_cap) {
		tcb_t *caller = ((tcb_t *)(cap_thread_cap_get_capTCBPtr(
			(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbCaller))->cap)));
		printf("caller_slot: %p_tcb\n", caller);
	}
	printf("}\n");
}
/* TBD: deal with nested cnodes */
void obj_cnode_print_slots(tcb_t *tcb)
{
	cap_t root = (((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbCTable))->cap;
	if (cap_get_capType(root) != cap_cnode_cap) {
		return;
	}
	word_t radix = cap_cnode_cap_get_capCNodeRadix(root);
	if (seen(root)) {
		return;
	}
	add_to_seen(root);
	printf("%p_cnode {\n", (void *)cap_cnode_cap_get_capCNodePtr(root));
	for (uint32_t i = 0; i < (1 << radix); i++) {
		lookupCapAndSlot_ret_t c = lookupCapAndSlot(tcb, i);
		if (cap_get_capType(c.cap) != cap_null_cap) {
			printf("0x%x: ", i);
			print_cap(c.cap);
		}
	}
	printf("}\n");
	for (uint32_t i = 0; i < (1 << radix); i++) {
		lookupCapAndSlot_ret_t c = lookupCapAndSlot(tcb, i);
		if (cap_get_capType(c.cap) == cap_irq_handler_cap) {
			/* TBD: should instead print it from IRQNode */
			obj_irq_print_slots(c.cap);
		}
	}
}
void obj_irq_print_maps(void)
{
	printf("irq maps {\n");
	for (seL4_Word target = 0; target < 1; target++) {
		for (unsigned i = 0; i <= maxIRQ; i++) {
			irq_t irq = (i);
			if (isIRQActive(irq)) {
				cap_t cap = intStateIRQNode[(irq)].cap;
				if (cap_get_capType(cap) != cap_null_cap) {
					printf("%d: 0x%lx_%lu_irq\n", i, (long unsigned int)irq,
					       (long unsigned int)target);
				}
			}
		}
	}
	printf("}\n");
}
void obj_irq_print_slots(cap_t irq_cap)
{
	irq_t irq = (cap_irq_handler_cap_get_capIRQ(irq_cap));
	if (isIRQActive(irq)) {
		printf("0x%lx_%lu_irq {\n", (long unsigned int)irq, (long unsigned int)0);
		cap_t ntfn_cap = intStateIRQNode[(irq)].cap;
		if (cap_get_capType(ntfn_cap) != cap_null_cap) {
			printf("0x0: ");
			print_cap(ntfn_cap);
		}
		printf("}\n");
	}
}
void print_objects(void)
{
	for (tcb_t *curr = ksDebugTCBs; curr != NULL;
	     curr = ((debug_tcb_t *)(((cte_t *)((word_t)(curr) & ~((1ul << (11)) - 1ul))) +
				     (tcbCNodeEntries)))
			    ->tcbDebugNext) {
		if (root_or_idle_tcb(curr)) {
			continue;
		}
		/* print the contains of the tcb's vtable as objects */
		obj_tcb_print_vtable(curr);
	}
	for (tcb_t *curr = ksDebugTCBs; curr != NULL;
	     curr = ((debug_tcb_t *)(((cte_t *)((word_t)(curr) & ~((1ul << (11)) - 1ul))) +
				     (tcbCNodeEntries)))
			    ->tcbDebugNext) {
		if (root_or_idle_tcb(curr)) {
			continue;
		}
		/* print the tcb as objects */
		printf("%p_tcb = tcb ", curr);
		obj_tcb_print_attrs(curr);
		/* print the contains of the tcb's ctable as objects */
		if (cap_get_capType(
			    (((cte_t *)((word_t)(curr) & ~((1ul << (11)) - 1ul))) + (tcbCTable))
				    ->cap) == cap_cnode_cap) {
			obj_tcb_print_cnodes(
				(((cte_t *)((word_t)(curr) & ~((1ul << (11)) - 1ul))) + (tcbCTable))
					->cap,
				curr);
		}
	}
}
void print_caps(void)
{
	for (tcb_t *curr = ksDebugTCBs; curr != NULL;
	     curr = ((debug_tcb_t *)(((cte_t *)((word_t)(curr) & ~((1ul << (11)) - 1ul))) +
				     (tcbCNodeEntries)))
			    ->tcbDebugNext) {
		if (root_or_idle_tcb(curr)) {
			continue;
		}
		obj_cnode_print_slots(curr);
		obj_vtable_print_slots(curr);
		obj_tcb_print_slots(curr);
	}
}
void print_cap(cap_t cap)
{
	switch (cap_get_capType(cap)) {
	case cap_endpoint_cap: {
		printf("%p_ep ", (void *)cap_endpoint_cap_get_capEPPtr(cap));
		cap_ep_print_attrs(cap);
		break;
	}
	case cap_notification_cap: {
		printf("%p_notification ", (void *)cap_notification_cap_get_capNtfnPtr(cap));
		cap_ntfn_print_attrs(cap);
		break;
	}
	case cap_untyped_cap: {
		printf("%p_untyped\n", (void *)cap_untyped_cap_get_capPtr(cap));
		break;
	}
	case cap_thread_cap: {
		printf("%p_tcb\n", (void *)cap_thread_cap_get_capTCBPtr(cap));
		break;
	}
	case cap_cnode_cap: {
		printf("%p_cnode ", (void *)cap_cnode_cap_get_capCNodePtr(cap));
		cap_cnode_print_attrs(cap);
		break;
	}
	case cap_irq_control_cap: {
		printf("irq_control\n"); /* only one in the system */
		break;
	}
	case cap_irq_handler_cap: {
		printf("%p_%lu_irq\n", (void *)cap_irq_handler_cap_get_capIRQ(cap),
		       (long unsigned int)0);
		break;
	}
	default: {
		print_cap_arch(cap);
		break;
	}
	}
}
void print_object(cap_t cap)
{
	switch (cap_get_capType(cap)) {
	case cap_endpoint_cap: {
		printf("%p_ep = ep\n", (void *)cap_endpoint_cap_get_capEPPtr(cap));
		break;
	}
	case cap_notification_cap: {
		printf("%p_notification = notification\n",
		       (void *)cap_notification_cap_get_capNtfnPtr(cap));
		break;
	}
	case cap_thread_cap: {
		/* this object has already got handle by `print_objects` */
		break;
	}
	case cap_cnode_cap: {
	}
	case cap_irq_handler_cap: {
		printf("%p_%lu_irq = irq\n", (void *)cap_irq_handler_cap_get_capIRQ(cap),
		       (long unsigned int)0);
		break;
	}
	default:
		print_object_arch(cap);
		break;
	}
}
/* Switch the owner of the FPU to the given thread on local core. */
void switchLocalFpuOwner(user_fpu_state_t *new_owner)
{
	enableFpu();
	if (ksActiveFPUState) {
		saveFpuState(ksActiveFPUState);
	}
	if (new_owner) {
		ksFPURestoresSinceSwitch = 0;
		loadFpuState(new_owner);
	} else {
		disableFpu();
	}
	ksActiveFPUState = new_owner;
}
void switchFpuOwner(user_fpu_state_t *new_owner, word_t cpu)
{
	{
		switchLocalFpuOwner(new_owner);
	}
}
/* Handle an FPU fault.
 *
 * This CPU exception is thrown when userspace attempts to use the FPU while
 * it is disabled. We need to save the current state of the FPU, and hand
 * it over. */
exception_t handleFPUFault(void)
{
	/* If we have already given the FPU to the user, we should not reach here.
	 * This should only be able to occur on CPUs without an FPU at all, which
	 * we presumably are happy to assume will not be running seL4. */
	/* Otherwise, lazily switch over the FPU. */
	switchLocalFpuOwner(&ksCurThread->tcbArch.tcbContext.fpuState);
	return EXCEPTION_NONE;
}
/* Prepare for the deletion of the given thread. */
void fpuThreadDelete(tcb_t *thread)
{
	/* If the thread being deleted currently owns the FPU, switch away from it
	 * so that 'ksActiveFPUState' doesn't point to invalid memory. */
	if (nativeThreadUsingFPU(thread)) {
		switchFpuOwner(NULL, 0);
	}
}
typedef struct _out_wrap_t out_wrap_t;
/* handler defining how/where to actually output a buffer */
typedef void (*out_write_fn)(out_wrap_t *out, const char *buf, word_t len);
struct _out_wrap_t {
	const out_write_fn write;
	char *const buf;
	const word_t maxlen;
	word_t used;
};
/* printf_core() and its helpers call this to actually output something. The
 * parameter 'out_wrap' cam be NULL, e.g. when printf_core() is just caller to
 * validate the format string. In this case we do nothing.
 */
static void out(out_wrap_t *out_wrap, const char *buf, word_t len)
{
	if (out_wrap) {
		out_wrap->write(out_wrap, buf, len);
	}
}
/* An out_write_fn implementation to print the characters via putchar(). It is
 * guaranteed here that 'out' is not NULL. The current implementation also never
 * passes NULL for 'buf'. */
static void do_output_to_putchar(out_wrap_t *out, const char *buf, word_t len)
{
	if (buf) {
		while (len-- > 0) {
			putchar(*buf++);
		}
	}
}
/* An out_write_fn implementation to copy the buffer into the out buffer. It is
 * guaranteed here that 'out' is not NULL. The current implementation also never
 * passes NULL for 'buf'. */
static void do_output_to_buffer(out_wrap_t *out, const char *buf, word_t len)
{
	/* It's guaranteed here that 'out' is not NULL. The current implementation
	 * also never passes NULL for 'buf'. */
	if (buf && (out->used < out->maxlen)) {
		/* there is still space in the buffer*/
		word_t free = out->maxlen - out->used;
		if (len > free) {
			len = free;
		}
		memcpy(&out->buf[out->used], buf, len);
		out->used += len;
	}
}
/*
 *------------------------------------------------------------------------------
 * printf() core implementation
 *------------------------------------------------------------------------------
 */
static inline bool_t isdigit(char c)
{
	return c >= '0' && c <= '9';
}
/* Convenient bit representation for modifier flags, which all fall within 31
 * codepoints of the space character.
 */
/* State machine to accept length modifiers + conversion specifiers.
 * Result is 0 on failure, or an argument type to pop on success.
 */
enum {
	BARE,
	LPRE,
	LLPRE,
	HPRE,
	HHPRE,
	BIGLPRE,
	ZTPRE,
	JPRE,
	STOP,
	PTR,
	INT,
	UINT,
	ULLONG,
	LONG,
	ULONG,
	SHORT,
	USHORT,
	CHAR,
	UCHAR,
	WORDT,
	LLONG,
	NOARG,
	MAXSTATE
};
static const unsigned char states[]['z' - 'A' + 1] = {
	{
		/* 0: bare types */
		[('d') - 'A'] = INT,
		[('i') - 'A'] = INT,
		[('o') - 'A'] = UINT,
		[('u') - 'A'] = UINT,
		[('x') - 'A'] = UINT,
		[('X') - 'A'] = UINT,
		[('c') - 'A'] = CHAR,
		[('s') - 'A'] = PTR,
		[('p') - 'A'] = ULONG,
		[('n') - 'A'] = PTR,
		[('l') - 'A'] = LPRE,
		[('h') - 'A'] = HPRE,
		[('z') - 'A'] = ZTPRE,
		[('j') - 'A'] = JPRE,
		[('t') - 'A'] = ZTPRE,
	},
	{
		/* 1: l-prefixed */
		[('d') - 'A'] = LONG,
		[('i') - 'A'] = LONG,
		[('o') - 'A'] = ULONG,
		[('u') - 'A'] = ULONG,
		[('x') - 'A'] = ULONG,
		[('X') - 'A'] = ULONG,
		[('n') - 'A'] = PTR,
		[('l') - 'A'] = LLPRE,
	},
	{
		/* 2: ll-prefixed */
		[('d') - 'A'] = LLONG,
		[('i') - 'A'] = LLONG,
		[('o') - 'A'] = ULLONG,
		[('u') - 'A'] = ULLONG,
		[('x') - 'A'] = ULLONG,
		[('X') - 'A'] = ULLONG,
		[('n') - 'A'] = PTR,
	},
	{
		/* 3: h-prefixed */
		[('d') - 'A'] = SHORT,
		[('i') - 'A'] = SHORT,
		[('o') - 'A'] = USHORT,
		[('u') - 'A'] = USHORT,
		[('x') - 'A'] = USHORT,
		[('X') - 'A'] = USHORT,
		[('n') - 'A'] = PTR,
		[('h') - 'A'] = HHPRE,
	},
	{
		/* 4: hh-prefixed */
		[('d') - 'A'] = CHAR,
		[('i') - 'A'] = CHAR,
		[('o') - 'A'] = UCHAR,
		[('u') - 'A'] = UCHAR,
		[('x') - 'A'] = UCHAR,
		[('X') - 'A'] = UCHAR,
		[('n') - 'A'] = PTR,
	},
	{
		/* 5: L-prefixed not supported */
	},
	{
		/* 6: z- or t-prefixed (assumed to be same size) */
		[('d') - 'A'] = LONG,
		[('i') - 'A'] = LONG,
		[('o') - 'A'] = WORDT,
		[('u') - 'A'] = WORDT,
		[('x') - 'A'] = WORDT,
		[('X') - 'A'] = WORDT,
		[('n') - 'A'] = PTR,
	},
	{
		/* 7: j-prefixed */
		[('d') - 'A'] = LLONG,
		[('i') - 'A'] = LLONG,
		[('o') - 'A'] = ULLONG,
		[('u') - 'A'] = ULLONG,
		[('x') - 'A'] = ULLONG,
		[('X') - 'A'] = ULLONG,
		[('n') - 'A'] = PTR,
	}};
union arg {
	uintmax_t i;
	long double f;
	void *p;
};
static void pop_arg(union arg *arg, int type, va_list *ap)
{
	switch (type) {
	case PTR:
		arg->p = __builtin_va_arg(*ap, void *);
		break;
	case INT:
		arg->i = __builtin_va_arg(*ap, int);
		break;
	case UINT:
		arg->i = __builtin_va_arg(*ap, unsigned int);
		break;
	case LONG:
		arg->i = __builtin_va_arg(*ap, long);
		break;
	case ULONG:
		arg->i = __builtin_va_arg(*ap, unsigned long);
		break;
	case LLONG:
		arg->i = __builtin_va_arg(*ap, long long);
		break;
	case ULLONG:
		arg->i = __builtin_va_arg(*ap, unsigned long long);
		break;
	case SHORT:
		arg->i = (short)__builtin_va_arg(*ap, int);
		break;
	case USHORT:
		arg->i = (unsigned short)__builtin_va_arg(*ap, int);
		break;
	case CHAR:
		arg->i = (signed char)__builtin_va_arg(*ap, int);
		break;
	case UCHAR:
		arg->i = (unsigned char)__builtin_va_arg(*ap, int);
		break;
	case WORDT:
		arg->i = __builtin_va_arg(*ap, word_t);
	}
}
static void pad(out_wrap_t *f, char c, int w, int l, int fl)
{
	char pad[32]; /* good enough for what the kernel prints */
	if (fl & ((1U << ('-' - ' ')) | (1U << ('0' - ' '))) || l >= w) {
		return;
	}
	l = w - l;
	memset(pad, c, l > sizeof(pad) ? sizeof(pad) : l);
	for (; l >= sizeof(pad); l -= sizeof(pad)) {
		out(f, pad, sizeof(pad));
	}
	out(f, pad, l);
}
static const char xdigits[16] = {"0123456789ABCDEF"};
static char *fmt_x(uintmax_t x, char *s, int lower)
{
	for (; x; x >>= 4) {
		*--s = xdigits[(x & 15)] | lower;
	}
	return s;
}
static char *fmt_o(uintmax_t x, char *s)
{
	for (; x; x >>= 3) {
		*--s = '0' + (x & 7);
	}
	return s;
}
static char *fmt_u(uintmax_t x, char *s)
{
	while (0 != x) {
		uintmax_t q = x / 10;
		unsigned int rem = x % 10;
		*--s = '0' + rem;
		x = q;
	}
	return s;
}
/* Maximum buffer size taken to ensure correct adaptation. However, it could be
 * reduced/removed if we could measure the buf length under all code paths
 */
static int getint(char **s)
{
	int i;
	for (i = 0; isdigit(**s); (*s)++) {
		if (i > (0xFFFFFFFFFFFFFFFF) / 10U || (**s - '0') > (0xFFFFFFFFFFFFFFFF) - 10 * i) {
			i = -1;
		} else {
			i = 10 * i + (**s - '0');
		}
	}
	return i;
}
static int printf_core(out_wrap_t *f, const char *fmt, va_list *ap, union arg *nl_arg, int *nl_type)
{
	char *a, *z, *s = (char *)fmt;
	unsigned l10n = 0, fl;
	int w, p, xp;
	union arg arg;
	int argpos;
	unsigned st, ps;
	int cnt = 0, l = 0;
	char buf[sizeof(uintmax_t) * 3 + 3 + 113 / 4];
	const char *prefix;
	int t, pl;
	for (;;) {
		if (l > (0xFFFFFFFFFFFFFFFF) - cnt) {
			/* This error is only specified for snprintf, for other function
			 * from the printf() family the behavior is unspecified. Stopping
			 * immediately here also seems sane, otherwise %n could produce
			 * wrong results.
			 */
			return -1; /* overflow */
		}
		/* Update output count, end loop when fmt is exhausted */
		cnt += l;
		if (!*s) {
			break;
		}
		/* Handle literal text and %% format specifiers */
		for (a = s; *s && *s != '%'; s++)
			;
		for (z = s; s[0] == '%' && s[1] == '%'; z++, s += 2)
			;
		if (z - a > (0xFFFFFFFFFFFFFFFF) - cnt) {
			return -1; /* overflow */
		}
		l = z - a;
		out(f, a, l);
		if (l) {
			continue;
		}
		if (isdigit(s[1]) && s[2] == '$') {
			l10n = 1;
			argpos = (s[1] - '0');
			s += 3;
		} else {
			argpos = -1;
			s++;
		}
		/* Read modifier flags */
		for (fl = 0; (unsigned)*s - ' ' < 32 &&
			     (((1U << ('#' - ' ')) | (1U << ('0' - ' ')) | (1U << ('-' - ' ')) |
			       (1U << (' ' - ' ')) | (1U << ('+' - ' ')) | (1U << ('\'' - ' '))) &
			      (1U << (*s - ' ')));
		     s++) {
			fl |= (1U << (*s - ' '));
		}
		/* Read field width */
		if (*s == '*') {
			if (isdigit(s[1]) && s[2] == '$') {
				l10n = 1;
				nl_type[(s[1] - '0')] = INT;
				w = nl_arg[(s[1] - '0')].i;
				s += 3;
			} else if (!l10n) {
				w = f ? __builtin_va_arg(*ap, int) : 0;
				s++;
			} else {
				return -1; /* invalid */
			}
			if (w < 0) {
				fl |= (1U << ('-' - ' '));
				w = -w;
			}
		} else if ((w = getint(&s)) < 0) {
			return -1; /* overflow */
		}
		/* Read precision */
		if (*s == '.' && s[1] == '*') {
			if (isdigit(s[2]) && s[3] == '$') {
				nl_type[(s[2] - '0')] = INT;
				p = nl_arg[(s[2] - '0')].i;
				s += 4;
			} else if (!l10n) {
				p = f ? __builtin_va_arg(*ap, int) : 0;
				s += 2;
			} else {
				return -1; /* invalid */
			}
			xp = (p >= 0);
		} else if (*s == '.') {
			s++;
			p = getint(&s);
			xp = 1;
		} else {
			p = -1;
			xp = 0;
		}
		/* Format specifier state machine */
		st = 0;
		do {
			if (((unsigned)(*s) - 'A' > 'z' - 'A')) {
				return -1; /* invalid */
			}
			ps = st;
			st = states[st][(*s++) - 'A'];
		} while (st - 1 < STOP);
		if (!st) {
			return -1; /* invalid */
		}
		/* Check validity of argument type (nl/normal) */
		if (st == NOARG) {
			if (argpos >= 0) {
				return -1; /* invalid */
			}
		} else {
			if (argpos >= 0) {
				nl_type[argpos] = st;
				arg = nl_arg[argpos];
			} else if (f) {
				pop_arg(&arg, st, ap);
			} else {
				return 0;
			}
		}
		if (!f) {
			continue;
		}
		z = buf + sizeof(buf);
		prefix = "-+   0X0x";
		pl = 0;
		t = s[-1];
		/* - and 0 flags are mutually exclusive */
		if (fl & (1U << ('-' - ' '))) {
			fl &= ~(1U << ('0' - ' '));
		}
		if (t == 'n') {
			if (!arg.p) {
				continue;
			}
			switch (ps) {
			case BARE:
				*(int *)arg.p = cnt;
				break;
			case LPRE:
				*(long *)arg.p = cnt;
				break;
			case LLPRE:
				*(long long *)arg.p = cnt;
				break;
			case HPRE:
				*(unsigned short *)arg.p = cnt;
				break;
			case HHPRE:
				*(unsigned char *)arg.p = cnt;
				break;
			case ZTPRE:
				*(word_t *)arg.p = cnt;
				break;
			case JPRE:
				*(word_t *)arg.p = cnt;
				break;
			}
			continue;
		} else if (t == 'c') {
			p = 1;
			a = z - p;
			*a = arg.i;
			fl &= ~(1U << ('0' - ' '));
		} else if (t == 's') {
			a = arg.p ? arg.p : "(null)";
			z = a + strnlen(a, p < 0 ? (0xFFFFFFFFFFFFFFFF) : p);
			if (p < 0 && *z) {
				return -1; /* overflow */
			}
			p = z - a;
			fl &= ~(1U << ('0' - ' '));
		} else {
			switch (t) {
			case 'p':
				p = (((p) > (2 * sizeof(void *))) ? (p) : (2 * sizeof(void *)));
				t = 'x';
				fl |= (1U << ('#' - ' '));
			case 'x':
			case 'X':
				a = fmt_x(arg.i, z, t & 32);
				if (arg.i && (fl & (1U << ('#' - ' ')))) {
					prefix += (t >> 4);
					pl = 2;
				}
				break;
			case 'o':
				a = fmt_o(arg.i, z);
				if ((fl & (1U << ('#' - ' '))) && p < (z - a + 1)) {
					p = z - a + 1;
				}
				break;
			case 'd':
			case 'i':
				pl = 1;
				if (arg.i > (0xFFFFFFFFFFFFFFFF)) {
					arg.i = -arg.i;
				} else if (fl & (1U << ('+' - ' '))) {
					prefix++;
				} else if (fl & (1U << (' ' - ' '))) {
					prefix += 2;
				} else {
					pl = 0;
				}
			case 'u':
				a = fmt_u(arg.i, z);
				break;
			}
			if (xp && p < 0) {
				return -1; /* overflow */
			}
			if (xp) {
				fl &= ~(1U << ('0' - ' '));
			}
			if (!arg.i && !p) {
				a = z;
			} else {
				p = (((p) > (z - a + !arg.i)) ? (p) : (z - a + !arg.i));
			}
		}
		if (p < z - a) {
			p = z - a;
		}
		if (p > (0xFFFFFFFFFFFFFFFF) - pl) {
			return -1; /* overflow */
		}
		if (w < pl + p) {
			w = pl + p;
		}
		if (w > (0xFFFFFFFFFFFFFFFF) - cnt) {
			return -1; /* overflow */
		}
		pad(f, ' ', w, pl + p, fl);
		out(f, prefix, pl);
		pad(f, '0', w, pl + p, fl ^ (1U << ('0' - ' ')));
		pad(f, '0', p, z - a, 0);
		out(f, a, z - a);
		pad(f, ' ', w, pl + p, fl ^ (1U << ('-' - ' ')));
		l = w;
	}
	if (f) {
		return cnt;
	}
	if (!l10n) {
		return 0;
	}
	int i;
	for (i = 1; i <= 9 && nl_type[i]; i++) {
		pop_arg(nl_arg + i, nl_type[i], ap);
	}
	for (; i <= 9 && !nl_type[i]; i++)
		;
	if (i <= 9) {
		return -1; /* invalid */
	}
	return 1;
}
static int vprintf(out_wrap_t *out, const char *fmt, va_list ap)
{
	va_list ap2;
	int nl_type[9 + 1] = {0};
	union arg nl_arg[9 + 1];
	int ret;
	/* validate format string */
	__builtin_va_copy(ap2, ap);
	if (printf_core(NULL, fmt, &ap2, nl_arg, nl_type) < 0) {
		__builtin_va_end(ap2);
		return -1;
	}
	ret = printf_core(out, fmt, &ap2, nl_arg, nl_type);
	__builtin_va_end(ap2);
	return ret;
}
/*
 *------------------------------------------------------------------------------
 * Kernel printing API
 *------------------------------------------------------------------------------
 */
int impl_kvprintf(const char *format, va_list ap)
{
	out_wrap_t out_wrap = {.write = do_output_to_putchar, .buf = NULL, .maxlen = 0, .used = 0};
	return vprintf(&out_wrap, format, ap);
}
int impl_ksnvprintf(char *str, word_t size, const char *format, va_list ap)
{
	if (!str) {
		size = 0;
	}
	out_wrap_t out_wrap = {.write = do_output_to_buffer, .buf = str, .maxlen = size, .used = 0};
	int ret = vprintf(&out_wrap, format, ap);
	/* We return the number of characters written into the buffer, excluding the
	 * terminating null char. However, we do never write more than 'size' bytes,
	 * that includes the terminating null char. If the output was truncated due
	 * to this limit, then the return value is the number of chars excluding the
	 * terminating null byte, which would have been written to the buffer, if
	 * enough space had been available. Thus, a return value of 'size' or more
	 * means that the output was truncated.
	 */
	if ((ret > 0) && (size > 0)) {
		str[(ret < size) ? ret : size - 1] = '\0';
	}
	return ret;
}
const register_t fault_messages[][(
	((n_syscallMessage) > (n_exceptionMessage)) ? (n_syscallMessage) : (n_exceptionMessage))] =
	{
		[MessageID_Syscall] = {[seL4_UnknownSyscall_X0] = X0,
				       [seL4_UnknownSyscall_X1] = X1,
				       [seL4_UnknownSyscall_X2] = X2,
				       [seL4_UnknownSyscall_X3] = X3,
				       [seL4_UnknownSyscall_X4] = X4,
				       [seL4_UnknownSyscall_X5] = X5,
				       [seL4_UnknownSyscall_X6] = X6,
				       [seL4_UnknownSyscall_X7] = X7,
				       [seL4_UnknownSyscall_FaultIP] = FaultIP,
				       [seL4_UnknownSyscall_SP] = SP_EL0,
				       [seL4_UnknownSyscall_LR] = ELR_EL1,
				       [seL4_UnknownSyscall_SPSR] = SPSR_EL1},
		[MessageID_Exception] = {[seL4_UserException_FaultIP] = FaultIP,
					 [seL4_UserException_SP] = SP_EL0,
					 [seL4_UserException_SPSR] = SPSR_EL1},
};
exception_t preemptionPoint(void);
/*
 * Possibly preempt the current thread to allow an interrupt to be handled.
 */
exception_t preemptionPoint(void)
{
	/* Record that we have performed some work. */
	ksWorkUnitsCompleted++;
	/*
	 * If we have performed a non-trivial amount of work since last time we
	 * checked for preemption, and there is an interrupt pending, handle the
	 * interrupt.
	 *
	 * We avoid checking for pending IRQs every call, as our callers tend to
	 * call us in a tight loop and checking for pending IRQs can be quite slow.
	 */
	if (ksWorkUnitsCompleted >= 100) {
		ksWorkUnitsCompleted = 0;
		if (isIRQPending()) {
			return EXCEPTION_PREEMPTED;
		}
	}
	return EXCEPTION_NONE;
}
/* Collective cpu states, including both pre core architecture dependant and independent data */
;
/* Global count of how many cpus there are */
word_t ksNumCPUs;
/* Pointer to the head of the scheduler queue for each priority */
tcb_queue_t ksReadyQueues[(1 * 256)];
word_t ksReadyQueuesL1Bitmap[1];
word_t ksReadyQueuesL2Bitmap[1][((256 + (1 << 6) - 1) / (1 << 6))];
_Static_assert((((256 + (1 << 6) - 1) / (1 << 6)) - 1) <= (1 << 6),
	       "ksReadyQueuesL1BitmapBigEnough");
/* Current thread TCB pointer */
tcb_t *ksCurThread;
/* Idle thread TCB pointer */
tcb_t *ksIdleThread;
/* Values of 0 and ~0 encode ResumeCurrentThread and ChooseNewThread
 * respectively; other values encode SwitchToThread and must be valid
 * tcb pointers */
tcb_t *ksSchedulerAction;
/* Currently active FPU state, or NULL if there is no active FPU state */
user_fpu_state_t *ksActiveFPUState;
word_t ksFPURestoresSinceSwitch;
tcb_t *ksDebugTCBs;
/* Units of work we have completed since the last time we checked for
 * pending interrupts */
word_t ksWorkUnitsCompleted;
irq_state_t intStateIRQTable[(maxIRQ + 1)];
/* CNode containing interrupt handler endpoints - like all seL4 objects, this CNode needs to be
 * of a size that is a power of 2 and aligned to its size. */
cte_t intStateIRQNode[(1ul << ((8)))] __attribute__((__aligned__((1ul << ((8) + 5)))));
_Static_assert(sizeof(intStateIRQNode) >= (((maxIRQ + 1)) * sizeof(cte_t)), "irqCNodeSize");
;
/* Currently active domain */
dom_t ksCurDomain;
/* Domain timeslice remaining */
word_t ksDomainTime;
/* An index into ksDomSchedule for active domain and length. */
word_t ksDomScheduleIdx;
/* Only used by lockTLBEntry */
word_t tlbLockCount = 0;
/* Idle thread. */
char ksIdleThreadTCB[1][(1ul << (11))] __attribute__((__aligned__((1ul << ((11 - 1))))));
kernel_entry_t ksKernelEntry;
struct finaliseSlot_ret {
	exception_t status;
	bool_t success;
	cap_t cleanupInfo;
};
typedef struct finaliseSlot_ret finaliseSlot_ret_t;
static finaliseSlot_ret_t finaliseSlot(cte_t *slot, bool_t exposed);
static void emptySlot(cte_t *slot, cap_t cleanupInfo);
static exception_t reduceZombie(cte_t *slot, bool_t exposed);
exception_t decodeCNodeInvocation(word_t invLabel, word_t length, cap_t cap, word_t *buffer)
{
	lookupSlot_ret_t lu_ret;
	cte_t *destSlot;
	word_t index, w_bits;
	exception_t status;
	/* Haskell error: "decodeCNodeInvocation: invalid cap" */
	if (invLabel < CNodeRevoke || invLabel > CNodeSaveCaller) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNodeCap: Illegal "
			       "Operation attempted.>>\n",
			       0lu, __func__, 54, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (length < 2) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode operation: "
			       "Truncated message.>>\n",
			       0lu, __func__, 60, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	index = getSyscallArg(0, buffer);
	w_bits = getSyscallArg(1, buffer);
	lu_ret = lookupTargetSlot(cap, index, w_bits);
	if (lu_ret.status != EXCEPTION_NONE) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode operation: Target "
			       "slot invalid.>>\n",
			       0lu, __func__, 69, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		return lu_ret.status;
	}
	destSlot = lu_ret.slot;
	if (invLabel >= CNodeCopy && invLabel <= CNodeMutate) {
		cte_t *srcSlot;
		word_t srcIndex, srcDepth, capData;
		bool_t isMove;
		seL4_CapRights_t cap_rights;
		cap_t srcRoot, newCap;
		deriveCap_ret_t dc_ret;
		cap_t srcCap;
		if (length < 4 || current_extra_caps.excaprefs[0] == NULL) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode "
				       "Copy/Mint/Move/Mutate: Truncated message.>>\n"
				       "\n",
				       0lu, __func__, 84, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_TruncatedMessage;
			return EXCEPTION_SYSCALL_ERROR;
		}
		srcIndex = getSyscallArg(2, buffer);
		srcDepth = getSyscallArg(3, buffer);
		srcRoot = current_extra_caps.excaprefs[0]->cap;
		status = ensureEmptySlot(destSlot);
		if (status != EXCEPTION_NONE) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode "
				       "Copy/Mint/Move/Mutate: Destination not empty.>>\n",
				       0lu, __func__, 95, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			return status;
		}
		lu_ret = lookupSourceSlot(srcRoot, srcIndex, srcDepth);
		if (lu_ret.status != EXCEPTION_NONE) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode "
				       "Copy/Mint/Move/Mutate: Invalid source slot.>>\n",
				       0lu, __func__, 101, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			return lu_ret.status;
		}
		srcSlot = lu_ret.slot;
		if (cap_get_capType(srcSlot->cap) == cap_null_cap) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode "
				       "Copy/Mint/Move/Mutate: Source slot invalid or empty.>>\n",
				       0lu, __func__, 107, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_FailedLookup;
			current_syscall_error.failedLookupWasSource = 1;
			current_lookup_fault = lookup_fault_missing_capability_new(srcDepth);
			return EXCEPTION_SYSCALL_ERROR;
		}
		switch (invLabel) {
		case CNodeCopy:
			if (length < 5) {
				do {
					printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Truncated "
					       "message for CNode Copy operation.>>\n",
					       0lu, __func__, 119, ksCurThread,
					       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
									   ~((1ul << (11)) -
									     1ul))) +
								(tcbCNodeEntries)))
						       ->tcbName,
					       (word_t)getRestartPC(ksCurThread));
				} while (0);
				current_syscall_error.type = seL4_TruncatedMessage;
				return EXCEPTION_SYSCALL_ERROR;
			}
			cap_rights = rightsFromWord(getSyscallArg(4, buffer));
			srcCap = maskCapRights(cap_rights, srcSlot->cap);
			dc_ret = deriveCap(srcSlot, srcCap);
			if (dc_ret.status != EXCEPTION_NONE) {
				do {
					printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Error "
					       "deriving cap for CNode Copy operation.>>\n",
					       0lu, __func__, 128, ksCurThread,
					       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
									   ~((1ul << (11)) -
									     1ul))) +
								(tcbCNodeEntries)))
						       ->tcbName,
					       (word_t)getRestartPC(ksCurThread));
				} while (0);
				return dc_ret.status;
			}
			newCap = dc_ret.cap;
			isMove = false;
			break;
		case CNodeMint:
			if (length < 6) {
				do {
					printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode "
					       "Mint: Truncated message.>>\n",
					       0lu, __func__, 138, ksCurThread,
					       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
									   ~((1ul << (11)) -
									     1ul))) +
								(tcbCNodeEntries)))
						       ->tcbName,
					       (word_t)getRestartPC(ksCurThread));
				} while (0);
				current_syscall_error.type = seL4_TruncatedMessage;
				return EXCEPTION_SYSCALL_ERROR;
			}
			cap_rights = rightsFromWord(getSyscallArg(4, buffer));
			capData = getSyscallArg(5, buffer);
			srcCap = maskCapRights(cap_rights, srcSlot->cap);
			dc_ret = deriveCap(srcSlot, updateCapData(false, capData, srcCap));
			if (dc_ret.status != EXCEPTION_NONE) {
				do {
					printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Error "
					       "deriving cap for CNode Mint operation.>>\n",
					       0lu, __func__, 149, ksCurThread,
					       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
									   ~((1ul << (11)) -
									     1ul))) +
								(tcbCNodeEntries)))
						       ->tcbName,
					       (word_t)getRestartPC(ksCurThread));
				} while (0);
				return dc_ret.status;
			}
			newCap = dc_ret.cap;
			isMove = false;
			break;
		case CNodeMove:
			newCap = srcSlot->cap;
			isMove = true;
			break;
		case CNodeMutate:
			if (length < 5) {
				do {
					printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode "
					       "Mutate: Truncated message.>>\n",
					       0lu, __func__, 165, ksCurThread,
					       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
									   ~((1ul << (11)) -
									     1ul))) +
								(tcbCNodeEntries)))
						       ->tcbName,
					       (word_t)getRestartPC(ksCurThread));
				} while (0);
				current_syscall_error.type = seL4_TruncatedMessage;
				return EXCEPTION_SYSCALL_ERROR;
			}
			capData = getSyscallArg(4, buffer);
			newCap = updateCapData(true, capData, srcSlot->cap);
			isMove = true;
			break;
		default:
			return EXCEPTION_NONE;
		}
		if (cap_get_capType(newCap) == cap_null_cap) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode "
				       "Copy/Mint/Move/Mutate: Mutated cap would be invalid.>>\n",
				       0lu, __func__, 182, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_IllegalOperation;
			return EXCEPTION_SYSCALL_ERROR;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		if (isMove) {
			return invokeCNodeMove(newCap, srcSlot, destSlot);
		} else {
			return invokeCNodeInsert(newCap, srcSlot, destSlot);
		}
	}
	if (invLabel == CNodeRevoke) {
		setThreadState(ksCurThread, ThreadState_Restart);
		return invokeCNodeRevoke(destSlot);
	}
	if (invLabel == CNodeDelete) {
		setThreadState(ksCurThread, ThreadState_Restart);
		return invokeCNodeDelete(destSlot);
	}
	if (invLabel == CNodeSaveCaller) {
		status = ensureEmptySlot(destSlot);
		if (status != EXCEPTION_NONE) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode SaveCaller: "
				       "Destination slot not empty.>>\n",
				       0lu, __func__, 209, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			return status;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return invokeCNodeSaveCaller(destSlot);
	}
	if (invLabel == CNodeCancelBadgedSends) {
		cap_t destCap;
		destCap = destSlot->cap;
		if (!hasCancelSendRights(destCap)) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode "
				       "CancelBadgedSends: Target cap invalid.>>\n",
				       0lu, __func__, 224, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_IllegalOperation;
			return EXCEPTION_SYSCALL_ERROR;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return invokeCNodeCancelBadgedSends(destCap);
	}
	if (invLabel == CNodeRotate) {
		word_t pivotNewData, pivotIndex, pivotDepth;
		word_t srcNewData, srcIndex, srcDepth;
		cte_t *pivotSlot, *srcSlot;
		cap_t pivotRoot, srcRoot, newSrcCap, newPivotCap;
		if (length < 8 || current_extra_caps.excaprefs[0] == NULL ||
		    current_extra_caps.excaprefs[1] == NULL) {
			current_syscall_error.type = seL4_TruncatedMessage;
			return EXCEPTION_SYSCALL_ERROR;
		}
		pivotNewData = getSyscallArg(2, buffer);
		pivotIndex = getSyscallArg(3, buffer);
		pivotDepth = getSyscallArg(4, buffer);
		srcNewData = getSyscallArg(5, buffer);
		srcIndex = getSyscallArg(6, buffer);
		srcDepth = getSyscallArg(7, buffer);
		pivotRoot = current_extra_caps.excaprefs[0]->cap;
		srcRoot = current_extra_caps.excaprefs[1]->cap;
		lu_ret = lookupSourceSlot(srcRoot, srcIndex, srcDepth);
		if (lu_ret.status != EXCEPTION_NONE) {
			return lu_ret.status;
		}
		srcSlot = lu_ret.slot;
		lu_ret = lookupPivotSlot(pivotRoot, pivotIndex, pivotDepth);
		if (lu_ret.status != EXCEPTION_NONE) {
			return lu_ret.status;
		}
		pivotSlot = lu_ret.slot;
		if (pivotSlot == srcSlot || pivotSlot == destSlot) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode Rotate: "
				       "Pivot slot the same as source or dest slot.>>\n",
				       0lu, __func__, 266, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_IllegalOperation;
			return EXCEPTION_SYSCALL_ERROR;
		}
		if (srcSlot != destSlot) {
			status = ensureEmptySlot(destSlot);
			if (status != EXCEPTION_NONE) {
				return status;
			}
		}
		if (cap_get_capType(srcSlot->cap) == cap_null_cap) {
			current_syscall_error.type = seL4_FailedLookup;
			current_syscall_error.failedLookupWasSource = 1;
			current_lookup_fault = lookup_fault_missing_capability_new(srcDepth);
			return EXCEPTION_SYSCALL_ERROR;
		}
		if (cap_get_capType(pivotSlot->cap) == cap_null_cap) {
			current_syscall_error.type = seL4_FailedLookup;
			current_syscall_error.failedLookupWasSource = 0;
			current_lookup_fault = lookup_fault_missing_capability_new(pivotDepth);
			return EXCEPTION_SYSCALL_ERROR;
		}
		newSrcCap = updateCapData(true, srcNewData, srcSlot->cap);
		newPivotCap = updateCapData(true, pivotNewData, pivotSlot->cap);
		if (cap_get_capType(newSrcCap) == cap_null_cap) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode Rotate: "
				       "Source cap invalid.>>\n",
				       0lu, __func__, 296, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_IllegalOperation;
			return EXCEPTION_SYSCALL_ERROR;
		}
		if (cap_get_capType(newPivotCap) == cap_null_cap) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: CNode Rotate: "
				       "Pivot cap invalid.>>\n",
				       0lu, __func__, 302, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			current_syscall_error.type = seL4_IllegalOperation;
			return EXCEPTION_SYSCALL_ERROR;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return invokeCNodeRotate(newSrcCap, newPivotCap, srcSlot, pivotSlot, destSlot);
	}
	return EXCEPTION_NONE;
}
exception_t invokeCNodeRevoke(cte_t *destSlot)
{
	return cteRevoke(destSlot);
}
exception_t invokeCNodeDelete(cte_t *destSlot)
{
	return cteDelete(destSlot, true);
}
exception_t invokeCNodeCancelBadgedSends(cap_t cap)
{
	word_t badge = cap_endpoint_cap_get_capEPBadge(cap);
	if (badge) {
		endpoint_t *ep = (endpoint_t *)cap_endpoint_cap_get_capEPPtr(cap);
		cancelBadgedSends(ep, badge);
	}
	return EXCEPTION_NONE;
}
exception_t invokeCNodeInsert(cap_t cap, cte_t *srcSlot, cte_t *destSlot)
{
	cteInsert(cap, srcSlot, destSlot);
	return EXCEPTION_NONE;
}
exception_t invokeCNodeMove(cap_t cap, cte_t *srcSlot, cte_t *destSlot)
{
	cteMove(cap, srcSlot, destSlot);
	return EXCEPTION_NONE;
}
exception_t invokeCNodeRotate(cap_t cap1, cap_t cap2, cte_t *slot1, cte_t *slot2, cte_t *slot3)
{
	if (slot1 == slot3) {
		cteSwap(cap1, slot1, cap2, slot2);
	} else {
		cteMove(cap2, slot2, slot3);
		cteMove(cap1, slot1, slot2);
	}
	return EXCEPTION_NONE;
}
exception_t invokeCNodeSaveCaller(cte_t *destSlot)
{
	cap_t cap;
	cte_t *srcSlot;
	srcSlot = (((cte_t *)((word_t)(ksCurThread) & ~((1ul << (11)) - 1ul))) + (tcbCaller));
	cap = srcSlot->cap;
	switch (cap_get_capType(cap)) {
	case cap_null_cap:
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "CNode SaveCaller: Reply cap not present."
			       ">>"
			       "\n",
			       0lu, __func__, 374, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		break;
	case cap_reply_cap:
		if (!cap_reply_cap_get_capReplyMaster(cap)) {
			cteMove(cap, srcSlot, destSlot);
		}
		break;
	default:
		_fail("caller capability must be null or reply",
		      "/home/lab/projects/seL4/seL4test/kernel/src/object/cnode.c", 384, __func__);
		break;
	}
	return EXCEPTION_NONE;
}
/*
 * If creating a child UntypedCap, don't allow new objects to be created in the
 * parent.
 */
static void setUntypedCapAsFull(cap_t srcCap, cap_t newCap, cte_t *srcSlot)
{
	if ((cap_get_capType(srcCap) == cap_untyped_cap) &&
	    (cap_get_capType(newCap) == cap_untyped_cap)) {
		if ((cap_untyped_cap_get_capPtr(srcCap) == cap_untyped_cap_get_capPtr(newCap)) &&
		    (cap_untyped_cap_get_capBlockSize(newCap) ==
		     cap_untyped_cap_get_capBlockSize(srcCap))) {
			cap_untyped_cap_ptr_set_capFreeIndex(
				&(srcSlot->cap),
				((1ul << ((cap_untyped_cap_get_capBlockSize(srcCap)) - 4))));
		}
	}
}
void cteInsert(cap_t newCap, cte_t *srcSlot, cte_t *destSlot)
{
	mdb_node_t srcMDB, newMDB;
	cap_t srcCap;
	bool_t newCapIsRevocable;
	srcMDB = srcSlot->cteMDBNode;
	srcCap = srcSlot->cap;
	newCapIsRevocable = isCapRevocable(newCap, srcCap);
	newMDB = mdb_node_set_mdbPrev(srcMDB, ((word_t)(srcSlot)));
	newMDB = mdb_node_set_mdbRevocable(newMDB, newCapIsRevocable);
	newMDB = mdb_node_set_mdbFirstBadged(newMDB, newCapIsRevocable);
	/* Haskell error: "cteInsert to non-empty destination" */
	/* Haskell error: "cteInsert: mdb entry must be empty" */
	/* Prevent parent untyped cap from being used again if creating a child
	 * untyped from it. */
	setUntypedCapAsFull(srcCap, newCap, srcSlot);
	destSlot->cap = newCap;
	destSlot->cteMDBNode = newMDB;
	mdb_node_ptr_set_mdbNext(&srcSlot->cteMDBNode, ((word_t)(destSlot)));
	if (mdb_node_get_mdbNext(newMDB)) {
		mdb_node_ptr_set_mdbPrev(&((cte_t *)(mdb_node_get_mdbNext(newMDB)))->cteMDBNode,
					 ((word_t)(destSlot)));
	}
}
void cteMove(cap_t newCap, cte_t *srcSlot, cte_t *destSlot)
{
	mdb_node_t mdb;
	word_t prev_ptr, next_ptr;
	/* Haskell error: "cteMove to non-empty destination" */
	/* Haskell error: "cteMove: mdb entry must be empty" */
	mdb = srcSlot->cteMDBNode;
	destSlot->cap = newCap;
	srcSlot->cap = cap_null_cap_new();
	destSlot->cteMDBNode = mdb;
	srcSlot->cteMDBNode = mdb_node_new(0, false, false, 0);
	prev_ptr = mdb_node_get_mdbPrev(mdb);
	if (prev_ptr)
		mdb_node_ptr_set_mdbNext(&((cte_t *)(prev_ptr))->cteMDBNode, ((word_t)(destSlot)));
	next_ptr = mdb_node_get_mdbNext(mdb);
	if (next_ptr)
		mdb_node_ptr_set_mdbPrev(&((cte_t *)(next_ptr))->cteMDBNode, ((word_t)(destSlot)));
}
void capSwapForDelete(cte_t *slot1, cte_t *slot2)
{
	cap_t cap1, cap2;
	if (slot1 == slot2) {
		return;
	}
	cap1 = slot1->cap;
	cap2 = slot2->cap;
	cteSwap(cap1, slot1, cap2, slot2);
}
void cteSwap(cap_t cap1, cte_t *slot1, cap_t cap2, cte_t *slot2)
{
	mdb_node_t mdb1, mdb2;
	word_t next_ptr, prev_ptr;
	slot1->cap = cap2;
	slot2->cap = cap1;
	mdb1 = slot1->cteMDBNode;
	prev_ptr = mdb_node_get_mdbPrev(mdb1);
	if (prev_ptr)
		mdb_node_ptr_set_mdbNext(&((cte_t *)(prev_ptr))->cteMDBNode, ((word_t)(slot2)));
	next_ptr = mdb_node_get_mdbNext(mdb1);
	if (next_ptr)
		mdb_node_ptr_set_mdbPrev(&((cte_t *)(next_ptr))->cteMDBNode, ((word_t)(slot2)));
	mdb2 = slot2->cteMDBNode;
	slot1->cteMDBNode = mdb2;
	slot2->cteMDBNode = mdb1;
	prev_ptr = mdb_node_get_mdbPrev(mdb2);
	if (prev_ptr)
		mdb_node_ptr_set_mdbNext(&((cte_t *)(prev_ptr))->cteMDBNode, ((word_t)(slot1)));
	next_ptr = mdb_node_get_mdbNext(mdb2);
	if (next_ptr)
		mdb_node_ptr_set_mdbPrev(&((cte_t *)(next_ptr))->cteMDBNode, ((word_t)(slot1)));
}
exception_t cteRevoke(cte_t *slot)
{
	cte_t *nextPtr;
	exception_t status;
	/* there is no need to check for a NullCap as NullCaps are
	   always accompanied by null mdb pointers */
	for (nextPtr = ((cte_t *)(mdb_node_get_mdbNext(slot->cteMDBNode)));
	     nextPtr && isMDBParentOf(slot, nextPtr);
	     nextPtr = ((cte_t *)(mdb_node_get_mdbNext(slot->cteMDBNode)))) {
		status = cteDelete(nextPtr, true);
		if (status != EXCEPTION_NONE) {
			return status;
		}
		status = preemptionPoint();
		if (status != EXCEPTION_NONE) {
			return status;
		}
	}
	return EXCEPTION_NONE;
}
exception_t cteDelete(cte_t *slot, bool_t exposed)
{
	finaliseSlot_ret_t fs_ret;
	fs_ret = finaliseSlot(slot, exposed);
	if (fs_ret.status != EXCEPTION_NONE) {
		return fs_ret.status;
	}
	if (exposed || fs_ret.success) {
		emptySlot(slot, fs_ret.cleanupInfo);
	}
	return EXCEPTION_NONE;
}
static void emptySlot(cte_t *slot, cap_t cleanupInfo)
{
	if (cap_get_capType(slot->cap) != cap_null_cap) {
		mdb_node_t mdbNode;
		cte_t *prev, *next;
		mdbNode = slot->cteMDBNode;
		prev = ((cte_t *)(mdb_node_get_mdbPrev(mdbNode)));
		next = ((cte_t *)(mdb_node_get_mdbNext(mdbNode)));
		if (prev) {
			mdb_node_ptr_set_mdbNext(&prev->cteMDBNode, ((word_t)(next)));
		}
		if (next) {
			mdb_node_ptr_set_mdbPrev(&next->cteMDBNode, ((word_t)(prev)));
		}
		if (next)
			mdb_node_ptr_set_mdbFirstBadged(
				&next->cteMDBNode, mdb_node_get_mdbFirstBadged(next->cteMDBNode) ||
							   mdb_node_get_mdbFirstBadged(mdbNode));
		slot->cap = cap_null_cap_new();
		slot->cteMDBNode = mdb_node_new(0, false, false, 0);
		postCapDeletion(cleanupInfo);
	}
}
static inline bool_t capRemovable(cap_t cap, cte_t *slot)
{
	switch (cap_get_capType(cap)) {
	case cap_null_cap:
		return true;
	case cap_zombie_cap: {
		word_t n = cap_zombie_cap_get_capZombieNumber(cap);
		cte_t *z_slot = (cte_t *)cap_zombie_cap_get_capZombiePtr(cap);
		return (n == 0 || (n == 1 && slot == z_slot));
	}
	default:
		_fail("finaliseCap should only return Zombie or NullCap",
		      "/home/lab/projects/seL4/seL4test/kernel/src/object/cnode.c", 605, __func__);
	}
}
static inline bool_t capCyclicZombie(cap_t cap, cte_t *slot)
{
	return cap_get_capType(cap) == cap_zombie_cap &&
	       ((cte_t *)(cap_zombie_cap_get_capZombiePtr(cap))) == slot;
}
static finaliseSlot_ret_t finaliseSlot(cte_t *slot, bool_t immediate)
{
	bool_t final;
	finaliseCap_ret_t fc_ret;
	exception_t status;
	finaliseSlot_ret_t ret;
	while (cap_get_capType(slot->cap) != cap_null_cap) {
		final = isFinalCapability(slot);
		fc_ret = finaliseCap(slot->cap, final, false);
		if (capRemovable(fc_ret.remainder, slot)) {
			ret.status = EXCEPTION_NONE;
			ret.success = true;
			ret.cleanupInfo = fc_ret.cleanupInfo;
			return ret;
		}
		slot->cap = fc_ret.remainder;
		if (!immediate && capCyclicZombie(fc_ret.remainder, slot)) {
			ret.status = EXCEPTION_NONE;
			ret.success = false;
			ret.cleanupInfo = fc_ret.cleanupInfo;
			return ret;
		}
		status = reduceZombie(slot, immediate);
		if (status != EXCEPTION_NONE) {
			ret.status = status;
			ret.success = false;
			ret.cleanupInfo = cap_null_cap_new();
			return ret;
		}
		status = preemptionPoint();
		if (status != EXCEPTION_NONE) {
			ret.status = status;
			ret.success = false;
			ret.cleanupInfo = cap_null_cap_new();
			return ret;
		}
	}
	ret.status = EXCEPTION_NONE;
	ret.success = true;
	ret.cleanupInfo = cap_null_cap_new();
	return ret;
}
static exception_t reduceZombie(cte_t *slot, bool_t immediate)
{
	cte_t *ptr;
	word_t n, type;
	exception_t status;
	ptr = (cte_t *)cap_zombie_cap_get_capZombiePtr(slot->cap);
	n = cap_zombie_cap_get_capZombieNumber(slot->cap);
	type = cap_zombie_cap_get_capZombieType(slot->cap);
	/* Haskell error: "reduceZombie: expected unremovable zombie" */
	if (immediate) {
		cte_t *endSlot = &ptr[n - 1];
		status = cteDelete(endSlot, false);
		if (status != EXCEPTION_NONE) {
			return status;
		}
		switch (cap_get_capType(slot->cap)) {
		case cap_null_cap:
			break;
		case cap_zombie_cap: {
			cte_t *ptr2 = (cte_t *)cap_zombie_cap_get_capZombiePtr(slot->cap);
			if (ptr == ptr2 && cap_zombie_cap_get_capZombieNumber(slot->cap) == n &&
			    cap_zombie_cap_get_capZombieType(slot->cap) == type) {
				slot->cap = cap_zombie_cap_set_capZombieNumber(slot->cap, n - 1);
			} else {
				/* Haskell error:
				 * "Expected new Zombie to be self-referential."
				 */
			}
			break;
		}
		default:
			_fail("Expected recursion to result in Zombie.",
			      "/home/lab/projects/seL4/seL4test/kernel/src/object/cnode.c", 710,
			      __func__);
		}
	} else {
		/* Haskell error: "Cyclic zombie passed to unexposed reduceZombie" */
		if (cap_get_capType(ptr->cap) == cap_zombie_cap) {
			/* Haskell error: "Moving self-referential Zombie aside." */
		}
		capSwapForDelete(ptr, slot);
	}
	return EXCEPTION_NONE;
}
void cteDeleteOne(cte_t *slot)
{
	word_t cap_type = cap_get_capType(slot->cap);
	if (cap_type != cap_null_cap) {
		bool_t final;
		finaliseCap_ret_t fc_ret;
		/** GHOSTUPD: "(gs_get_assn cteDeleteOne_'proc \<acute>ghost'state = (-1)
		    \<or> gs_get_assn cteDeleteOne_'proc \<acute>ghost'state = \<acute>cap_type,
		   id)" */
		final = isFinalCapability(slot);
		fc_ret = finaliseCap(slot->cap, final, true);
		/* Haskell error: "cteDeleteOne: cap should be removable" */
		emptySlot(slot, cap_null_cap_new());
	}
}
void insertNewCap(cte_t *parent, cte_t *slot, cap_t cap)
{
	cte_t *next;
	next = ((cte_t *)(mdb_node_get_mdbNext(parent->cteMDBNode)));
	slot->cap = cap;
	slot->cteMDBNode = mdb_node_new(((word_t)(next)), true, true, ((word_t)(parent)));
	if (next) {
		mdb_node_ptr_set_mdbPrev(&next->cteMDBNode, ((word_t)(slot)));
	}
	mdb_node_ptr_set_mdbNext(&parent->cteMDBNode, ((word_t)(slot)));
}
void setupReplyMaster(tcb_t *thread)
{
	cte_t *slot;
	slot = (((cte_t *)((word_t)(thread) & ~((1ul << (11)) - 1ul))) + (tcbReply));
	if (cap_get_capType(slot->cap) == cap_null_cap) {
		/* Haskell asserts that no reply caps exist for this thread here. This
		 * cannot be translated. */
		slot->cap = cap_reply_cap_new(true, true, ((word_t)(thread)));
		slot->cteMDBNode = mdb_node_new(0, false, false, 0);
		mdb_node_ptr_set_mdbRevocable(&slot->cteMDBNode, true);
		mdb_node_ptr_set_mdbFirstBadged(&slot->cteMDBNode, true);
	}
}
bool_t isMDBParentOf(cte_t *cte_a, cte_t *cte_b)
{
	if (!mdb_node_get_mdbRevocable(cte_a->cteMDBNode)) {
		return false;
	}
	if (!sameRegionAs(cte_a->cap, cte_b->cap)) {
		return false;
	}
	switch (cap_get_capType(cte_a->cap)) {
	case cap_endpoint_cap: {
		word_t badge;
		badge = cap_endpoint_cap_get_capEPBadge(cte_a->cap);
		if (badge == 0) {
			return true;
		}
		return (badge == cap_endpoint_cap_get_capEPBadge(cte_b->cap)) &&
		       !mdb_node_get_mdbFirstBadged(cte_b->cteMDBNode);
		break;
	}
	case cap_notification_cap: {
		word_t badge;
		badge = cap_notification_cap_get_capNtfnBadge(cte_a->cap);
		if (badge == 0) {
			return true;
		}
		return (badge == cap_notification_cap_get_capNtfnBadge(cte_b->cap)) &&
		       !mdb_node_get_mdbFirstBadged(cte_b->cteMDBNode);
		break;
	}
	default:
		return true;
		break;
	}
}
exception_t ensureNoChildren(cte_t *slot)
{
	if (mdb_node_get_mdbNext(slot->cteMDBNode) != 0) {
		cte_t *next;
		next = ((cte_t *)(mdb_node_get_mdbNext(slot->cteMDBNode)));
		if (isMDBParentOf(slot, next)) {
			current_syscall_error.type = seL4_RevokeFirst;
			return EXCEPTION_SYSCALL_ERROR;
		}
	}
	return EXCEPTION_NONE;
}
exception_t ensureEmptySlot(cte_t *slot)
{
	if (cap_get_capType(slot->cap) != cap_null_cap) {
		current_syscall_error.type = seL4_DeleteFirst;
		return EXCEPTION_SYSCALL_ERROR;
	}
	return EXCEPTION_NONE;
}
bool_t isFinalCapability(cte_t *cte)
{
	mdb_node_t mdb;
	bool_t prevIsSameObject;
	mdb = cte->cteMDBNode;
	if (mdb_node_get_mdbPrev(mdb) == 0) {
		prevIsSameObject = false;
	} else {
		cte_t *prev;
		prev = ((cte_t *)(mdb_node_get_mdbPrev(mdb)));
		prevIsSameObject = sameObjectAs(prev->cap, cte->cap);
	}
	if (prevIsSameObject) {
		return false;
	} else {
		if (mdb_node_get_mdbNext(mdb) == 0) {
			return true;
		} else {
			cte_t *next;
			next = ((cte_t *)(mdb_node_get_mdbNext(mdb)));
			return !sameObjectAs(cte->cap, next->cap);
		}
	}
}
bool_t slotCapLongRunningDelete(cte_t *slot)
{
	if (cap_get_capType(slot->cap) == cap_null_cap) {
		return false;
	} else if (!isFinalCapability(slot)) {
		return false;
	}
	switch (cap_get_capType(slot->cap)) {
	case cap_thread_cap:
	case cap_zombie_cap:
	case cap_cnode_cap:
		return true;
	default:
		return false;
	}
}
/* This implementation is specialised to the (current) limit
 * of one cap receive slot. */
cte_t *getReceiveSlots(tcb_t *thread, word_t *buffer)
{
	cap_transfer_t ct;
	cptr_t cptr;
	lookupCap_ret_t luc_ret;
	lookupSlot_ret_t lus_ret;
	cte_t *slot;
	cap_t cnode;
	if (!buffer) {
		return NULL;
	}
	ct = loadCapTransfer(buffer);
	cptr = ct.ctReceiveRoot;
	luc_ret = lookupCap(thread, cptr);
	if (luc_ret.status != EXCEPTION_NONE) {
		return NULL;
	}
	cnode = luc_ret.cap;
	lus_ret = lookupTargetSlot(cnode, ct.ctReceiveIndex, ct.ctReceiveDepth);
	if (lus_ret.status != EXCEPTION_NONE) {
		return NULL;
	}
	slot = lus_ret.slot;
	if (cap_get_capType(slot->cap) != cap_null_cap) {
		return NULL;
	}
	return slot;
}
cap_transfer_t loadCapTransfer(word_t *buffer)
{
	const int offset = seL4_MsgMaxLength + ((1ul << (seL4_MsgExtraCapBits)) - 1) + 2;
	return capTransferFromWords(buffer + offset);
}
static inline void ep_ptr_set_queue(endpoint_t *epptr, tcb_queue_t queue)
{
	endpoint_ptr_set_epQueue_head(epptr, (word_t)queue.head);
	endpoint_ptr_set_epQueue_tail(epptr, (word_t)queue.end);
}
void sendIPC(bool_t blocking, bool_t do_call, word_t badge, bool_t canGrant, bool_t canGrantReply,
	     tcb_t *thread, endpoint_t *epptr)
{
	switch (endpoint_ptr_get_state(epptr)) {
	case EPState_Idle:
	case EPState_Send:
		if (blocking) {
			tcb_queue_t queue;
			/* Set thread state to BlockedOnSend */
			thread_state_ptr_set_tsType(&thread->tcbState, ThreadState_BlockedOnSend);
			thread_state_ptr_set_blockingObject(&thread->tcbState, ((word_t)(epptr)));
			thread_state_ptr_set_blockingIPCBadge(&thread->tcbState, badge);
			thread_state_ptr_set_blockingIPCCanGrant(&thread->tcbState, canGrant);
			thread_state_ptr_set_blockingIPCCanGrantReply(&thread->tcbState,
								      canGrantReply);
			thread_state_ptr_set_blockingIPCIsCall(&thread->tcbState, do_call);
			scheduleTCB(thread);
			/* Place calling thread in endpoint queue */
			queue = ep_ptr_get_queue(epptr);
			queue = tcbEPAppend(thread, queue);
			endpoint_ptr_set_state(epptr, EPState_Send);
			ep_ptr_set_queue(epptr, queue);
		}
		break;
	case EPState_Recv: {
		tcb_queue_t queue;
		tcb_t *dest;
		/* Get the head of the endpoint queue. */
		queue = ep_ptr_get_queue(epptr);
		dest = queue.head;
		/* Haskell error "Receive endpoint queue must not be empty" */
		/* Dequeue the first TCB */
		queue = tcbEPDequeue(dest, queue);
		ep_ptr_set_queue(epptr, queue);
		if (!queue.head) {
			endpoint_ptr_set_state(epptr, EPState_Idle);
		}
		/* Do the transfer */
		doIPCTransfer(thread, epptr, badge, canGrant, dest);
		bool_t replyCanGrant = thread_state_ptr_get_blockingIPCCanGrant(&dest->tcbState);
		setThreadState(dest, ThreadState_Running);
		possibleSwitchTo(dest);
		if (do_call) {
			if (canGrant || canGrantReply) {
				setupCallerCap(thread, dest, replyCanGrant);
			} else {
				setThreadState(thread, ThreadState_Inactive);
			}
		}
		break;
	}
	}
}
void receiveIPC(tcb_t *thread, cap_t cap, bool_t isBlocking)
{
	endpoint_t *epptr;
	notification_t *ntfnPtr;
	/* Haskell error "receiveIPC: invalid cap" */
	epptr = ((endpoint_t *)(cap_endpoint_cap_get_capEPPtr(cap)));
	/* Check for anything waiting in the notification */
	ntfnPtr = thread->tcbBoundNotification;
	if (ntfnPtr && notification_ptr_get_state(ntfnPtr) == NtfnState_Active) {
		completeSignal(ntfnPtr, thread);
	} else {
		switch (endpoint_ptr_get_state(epptr)) {
		case EPState_Idle:
		case EPState_Recv: {
			tcb_queue_t queue;
			if (isBlocking) {
				/* Set thread state to BlockedOnReceive */
				thread_state_ptr_set_tsType(&thread->tcbState,
							    ThreadState_BlockedOnReceive);
				thread_state_ptr_set_blockingObject(&thread->tcbState,
								    ((word_t)(epptr)));
				thread_state_ptr_set_blockingIPCCanGrant(
					&thread->tcbState, cap_endpoint_cap_get_capCanGrant(cap));
				scheduleTCB(thread);
				/* Place calling thread in endpoint queue */
				queue = ep_ptr_get_queue(epptr);
				queue = tcbEPAppend(thread, queue);
				endpoint_ptr_set_state(epptr, EPState_Recv);
				ep_ptr_set_queue(epptr, queue);
			} else {
				doNBRecvFailedTransfer(thread);
			}
			break;
		}
		case EPState_Send: {
			tcb_queue_t queue;
			tcb_t *sender;
			word_t badge;
			bool_t canGrant;
			bool_t canGrantReply;
			bool_t do_call;
			/* Get the head of the endpoint queue. */
			queue = ep_ptr_get_queue(epptr);
			sender = queue.head;
			/* Haskell error "Send endpoint queue must not be empty" */
			/* Dequeue the first TCB */
			queue = tcbEPDequeue(sender, queue);
			ep_ptr_set_queue(epptr, queue);
			if (!queue.head) {
				endpoint_ptr_set_state(epptr, EPState_Idle);
			}
			/* Get sender IPC details */
			badge = thread_state_ptr_get_blockingIPCBadge(&sender->tcbState);
			canGrant = thread_state_ptr_get_blockingIPCCanGrant(&sender->tcbState);
			canGrantReply =
				thread_state_ptr_get_blockingIPCCanGrantReply(&sender->tcbState);
			/* Do the transfer */
			doIPCTransfer(sender, epptr, badge, canGrant, thread);
			do_call = thread_state_ptr_get_blockingIPCIsCall(&sender->tcbState);
			if (do_call) {
				if (canGrant || canGrantReply) {
					setupCallerCap(sender, thread,
						       cap_endpoint_cap_get_capCanGrant(cap));
				} else {
					setThreadState(sender, ThreadState_Inactive);
				}
			} else {
				setThreadState(sender, ThreadState_Running);
				possibleSwitchTo(sender);
			}
			break;
		}
		}
	}
}
void replyFromKernel_error(tcb_t *thread)
{
	word_t len;
	word_t *ipcBuffer;
	ipcBuffer = lookupIPCBuffer(true, thread);
	setRegister(thread, badgeRegister, 0);
	len = setMRs_syscall_error(thread, ipcBuffer);
	setRegister(
		thread, msgInfoRegister,
		wordFromMessageInfo(seL4_MessageInfo_new(current_syscall_error.type, 0, 0, len)));
}
void replyFromKernel_success_empty(tcb_t *thread)
{
	setRegister(thread, badgeRegister, 0);
	setRegister(thread, msgInfoRegister, wordFromMessageInfo(seL4_MessageInfo_new(0, 0, 0, 0)));
}
void cancelIPC(tcb_t *tptr)
{
	thread_state_t *state = &tptr->tcbState;
	switch (thread_state_ptr_get_tsType(state)) {
	case ThreadState_BlockedOnSend:
	case ThreadState_BlockedOnReceive: {
		/* blockedIPCCancel state */
		endpoint_t *epptr;
		tcb_queue_t queue;
		epptr = ((endpoint_t *)(thread_state_ptr_get_blockingObject(state)));
		/* Haskell error "blockedIPCCancel: endpoint must not be idle" */
		/* Dequeue TCB */
		queue = ep_ptr_get_queue(epptr);
		queue = tcbEPDequeue(tptr, queue);
		ep_ptr_set_queue(epptr, queue);
		if (!queue.head) {
			endpoint_ptr_set_state(epptr, EPState_Idle);
		}
		setThreadState(tptr, ThreadState_Inactive);
		break;
	}
	case ThreadState_BlockedOnNotification:
		cancelSignal(tptr,
			     ((notification_t *)(thread_state_ptr_get_blockingObject(state))));
		break;
	case ThreadState_BlockedOnReply: {
		cte_t *slot, *callerCap;
		tptr->tcbFault = seL4_Fault_NullFault_new();
		/* Get the reply cap slot */
		slot = (((cte_t *)((word_t)(tptr) & ~((1ul << (11)) - 1ul))) + (tcbReply));
		callerCap = ((cte_t *)(mdb_node_get_mdbNext(slot->cteMDBNode)));
		if (callerCap) {
			/** GHOSTUPD: "(True,
			    gs_set_assn cteDeleteOne_'proc (ucast cap_reply_cap))" */
			cteDeleteOne(callerCap);
		}
		break;
	}
	}
}
void cancelAllIPC(endpoint_t *epptr)
{
	switch (endpoint_ptr_get_state(epptr)) {
	case EPState_Idle:
		break;
	default: {
		tcb_t *thread = ((tcb_t *)(endpoint_ptr_get_epQueue_head(epptr)));
		/* Make endpoint idle */
		endpoint_ptr_set_state(epptr, EPState_Idle);
		endpoint_ptr_set_epQueue_head(epptr, 0);
		endpoint_ptr_set_epQueue_tail(epptr, 0);
		/* Set all blocked threads to restart */
		for (; thread; thread = thread->tcbEPNext) {
			setThreadState(thread, ThreadState_Restart);
			tcbSchedEnqueue(thread);
		}
		rescheduleRequired();
		break;
	}
	}
}
void cancelBadgedSends(endpoint_t *epptr, word_t badge)
{
	switch (endpoint_ptr_get_state(epptr)) {
	case EPState_Idle:
	case EPState_Recv:
		break;
	case EPState_Send: {
		tcb_t *thread, *next;
		tcb_queue_t queue = ep_ptr_get_queue(epptr);
		/* this is a de-optimisation for verification
		 * reasons. it allows the contents of the endpoint
		 * queue to be ignored during the for loop. */
		endpoint_ptr_set_state(epptr, EPState_Idle);
		endpoint_ptr_set_epQueue_head(epptr, 0);
		endpoint_ptr_set_epQueue_tail(epptr, 0);
		for (thread = queue.head; thread; thread = next) {
			word_t b = thread_state_ptr_get_blockingIPCBadge(&thread->tcbState);
			next = thread->tcbEPNext;
			if (b == badge) {
				setThreadState(thread, ThreadState_Restart);
				tcbSchedEnqueue(thread);
				queue = tcbEPDequeue(thread, queue);
			}
		}
		ep_ptr_set_queue(epptr, queue);
		if (queue.head) {
			endpoint_ptr_set_state(epptr, EPState_Send);
		}
		rescheduleRequired();
		break;
	}
	default:
		_fail("invalid EP state",
		      "/home/lab/projects/seL4/seL4test/kernel/src/object/endpoint.c", 497,
		      __func__);
	}
}
exception_t decodeIRQControlInvocation(word_t invLabel, word_t length, cte_t *srcSlot,
				       word_t *buffer)
{
	if (invLabel == IRQIssueIRQHandler) {
		word_t index, depth, irq_w;
		irq_t irq;
		cte_t *destSlot;
		cap_t cnodeCap;
		lookupSlot_ret_t lu_ret;
		exception_t status;
		if (length < 3 || current_extra_caps.excaprefs[0] == NULL) {
			current_syscall_error.type = seL4_TruncatedMessage;
			return EXCEPTION_SYSCALL_ERROR;
		}
		irq_w = getSyscallArg(0, buffer);
		irq = (irq_w);
		index = getSyscallArg(1, buffer);
		depth = getSyscallArg(2, buffer);
		cnodeCap = current_extra_caps.excaprefs[0]->cap;
		status = Arch_checkIRQ(irq_w);
		if (status != EXCEPTION_NONE) {
			return status;
		}
		if (isIRQActive(irq)) {
			current_syscall_error.type = seL4_RevokeFirst;
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Rejecting request "
				       "for IRQ %u. Already active.>>\n",
				       0lu, __func__, 52, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread), (int)(irq));
			} while (0);
			return EXCEPTION_SYSCALL_ERROR;
		}
		lu_ret = lookupTargetSlot(cnodeCap, index, depth);
		if (lu_ret.status != EXCEPTION_NONE) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Target slot for "
				       "new IRQ Handler cap invalid: cap %lu, IRQ %u.>>\n",
				       0lu, __func__, 58, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread), getExtraCPtr(buffer, 0),
				       (int)(irq));
			} while (0);
			return lu_ret.status;
		}
		destSlot = lu_ret.slot;
		status = ensureEmptySlot(destSlot);
		if (status != EXCEPTION_NONE) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Target slot for "
				       "new IRQ Handler cap not empty: cap %lu, IRQ %u.>>\n",
				       0lu, __func__, 66, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread), getExtraCPtr(buffer, 0),
				       (int)(irq));
			} while (0);
			return status;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return invokeIRQControl(irq, destSlot, srcSlot);
	} else {
		return Arch_decodeIRQControlInvocation(invLabel, length, srcSlot, buffer);
	}
}
exception_t invokeIRQControl(irq_t irq, cte_t *handlerSlot, cte_t *controlSlot)
{
	setIRQState(IRQSignal, irq);
	cteInsert(cap_irq_handler_cap_new((irq)), controlSlot, handlerSlot);
	return EXCEPTION_NONE;
}
exception_t decodeIRQHandlerInvocation(word_t invLabel, irq_t irq)
{
	switch (invLabel) {
	case IRQAckIRQ:
		setThreadState(ksCurThread, ThreadState_Restart);
		invokeIRQHandler_AckIRQ(irq);
		return EXCEPTION_NONE;
	case IRQSetIRQHandler: {
		cap_t ntfnCap;
		cte_t *slot;
		if (current_extra_caps.excaprefs[0] == NULL) {
			current_syscall_error.type = seL4_TruncatedMessage;
			return EXCEPTION_SYSCALL_ERROR;
		}
		ntfnCap = current_extra_caps.excaprefs[0]->cap;
		slot = current_extra_caps.excaprefs[0];
		if (cap_get_capType(ntfnCap) != cap_notification_cap ||
		    !cap_notification_cap_get_capNtfnCanSend(ntfnCap)) {
			if (cap_get_capType(ntfnCap) != cap_notification_cap) {
				do {
					printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: "
					       "IRQSetHandler: provided cap is not an notification "
					       "capability.>>\n",
					       0lu, __func__, 108, ksCurThread,
					       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
									   ~((1ul << (11)) -
									     1ul))) +
								(tcbCNodeEntries)))
						       ->tcbName,
					       (word_t)getRestartPC(ksCurThread));
				} while (0);
			} else {
				do {
					printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: "
					       "IRQSetHandler: caller does not have send rights on "
					       "the endpoint.>>\n",
					       0lu, __func__, 110, ksCurThread,
					       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
									   ~((1ul << (11)) -
									     1ul))) +
								(tcbCNodeEntries)))
						       ->tcbName,
					       (word_t)getRestartPC(ksCurThread));
				} while (0);
			}
			current_syscall_error.type = seL4_InvalidCapability;
			current_syscall_error.invalidCapNumber = 0;
			return EXCEPTION_SYSCALL_ERROR;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		invokeIRQHandler_SetIRQHandler(irq, ntfnCap, slot);
		return EXCEPTION_NONE;
	}
	case IRQClearIRQHandler:
		setThreadState(ksCurThread, ThreadState_Restart);
		invokeIRQHandler_ClearIRQHandler(irq);
		return EXCEPTION_NONE;
	default:
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: IRQHandler: Illegal "
			       "operation.>>\n",
			       0lu, __func__, 128, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
}
void invokeIRQHandler_AckIRQ(irq_t irq)
{
	maskInterrupt(false, irq);
}
void invokeIRQHandler_SetIRQHandler(irq_t irq, cap_t cap, cte_t *slot)
{
	cte_t *irqSlot;
	irqSlot = intStateIRQNode + (irq);
	/** GHOSTUPD: "(True, gs_set_assn cteDeleteOne_'proc (-1))" */
	cteDeleteOne(irqSlot);
	cteInsert(cap, slot, irqSlot);
}
void invokeIRQHandler_ClearIRQHandler(irq_t irq)
{
	cte_t *irqSlot;
	irqSlot = intStateIRQNode + (irq);
	/** GHOSTUPD: "(True, gs_set_assn cteDeleteOne_'proc (-1))" */
	cteDeleteOne(irqSlot);
}
void deletingIRQHandler(irq_t irq)
{
	cte_t *slot;
	slot = intStateIRQNode + (irq);
	/** GHOSTUPD: "(True, gs_set_assn cteDeleteOne_'proc (ucast cap_notification_cap))" */
	cteDeleteOne(slot);
}
void deletedIRQHandler(irq_t irq)
{
	setIRQState(IRQInactive, irq);
}
void handleInterrupt(irq_t irq)
{
	if (__builtin_expect(!!((irq) > maxIRQ), 0)) {
		/* The interrupt number is out of range. Pretend it did not happen by
		 * handling it like an inactive interrupt (mask and ack). We assume this
		 * is acceptable, because the platform specific interrupt controller
		 * driver reported this interrupt. Maybe the value maxIRQ is just wrong
		 * or set to a lower value because the interrupts are unused.
		 */
		printf("Received IRQ %d, which is above the platforms maxIRQ of %d\n", (int)(irq),
		       (int)maxIRQ);
		maskInterrupt(true, irq);
		ackInterrupt(irq);
		return;
	}
	switch (intStateIRQTable[(irq)]) {
	case IRQSignal: {
		/* Merging the variable declaration and initialization into one line
		 * requires an update in the proofs first. Might be a c89 legacy.
		 */
		cap_t cap;
		cap = intStateIRQNode[(irq)].cap;
		if (cap_get_capType(cap) == cap_notification_cap &&
		    cap_notification_cap_get_capNtfnCanSend(cap)) {
			sendSignal(((notification_t *)(cap_notification_cap_get_capNtfnPtr(cap))),
				   cap_notification_cap_get_capNtfnBadge(cap));
		} else {
			printf("Undelivered IRQ: %d\n", (int)(irq));
		}
		maskInterrupt(true, irq);
		break;
	}
	case IRQTimer:
		timerTick();
		resetTimer();
		break;
	case IRQReserved:
		handleReservedIRQ(irq);
		break;
	case IRQInactive:
		/* This case shouldn't happen anyway unless the hardware or platform
		 * code is broken. Hopefully masking it again should make the interrupt
		 * go away.
		 */
		maskInterrupt(true, irq);
		printf("Received disabled IRQ: %d\n", (int)(irq));
		break;
	default:
		/* No corresponding haskell error */
		_fail("Invalid IRQ state",
		      "/home/lab/projects/seL4/seL4test/kernel/src/object/interrupt.c", 252,
		      __func__);
	}
	/* Every interrupt is ack'd, even if it is an inactive one. Rationale is,
	 * that for any interrupt reported by the platform specific code the generic
	 * kernel code does report here that it is done with handling it. */
	ackInterrupt(irq);
}
bool_t isIRQActive(irq_t irq)
{
	return intStateIRQTable[(irq)] != IRQInactive;
}
void setIRQState(irq_state_t irqState, irq_t irq)
{
	intStateIRQTable[(irq)] = irqState;
	maskInterrupt(irqState == IRQInactive, irq);
}
static inline tcb_queue_t ntfn_ptr_get_queue(notification_t *ntfnPtr)
{
	tcb_queue_t ntfn_queue;
	ntfn_queue.head = (tcb_t *)notification_ptr_get_ntfnQueue_head(ntfnPtr);
	ntfn_queue.end = (tcb_t *)notification_ptr_get_ntfnQueue_tail(ntfnPtr);
	return ntfn_queue;
}
static inline void ntfn_ptr_set_queue(notification_t *ntfnPtr, tcb_queue_t ntfn_queue)
{
	notification_ptr_set_ntfnQueue_head(ntfnPtr, (word_t)ntfn_queue.head);
	notification_ptr_set_ntfnQueue_tail(ntfnPtr, (word_t)ntfn_queue.end);
}
static inline void ntfn_set_active(notification_t *ntfnPtr, word_t badge)
{
	notification_ptr_set_state(ntfnPtr, NtfnState_Active);
	notification_ptr_set_ntfnMsgIdentifier(ntfnPtr, badge);
}
void sendSignal(notification_t *ntfnPtr, word_t badge)
{
	switch (notification_ptr_get_state(ntfnPtr)) {
	case NtfnState_Idle: {
		tcb_t *tcb = (tcb_t *)notification_ptr_get_ntfnBoundTCB(ntfnPtr);
		/* Check if we are bound and that thread is waiting for a message */
		if (tcb) {
			if (thread_state_ptr_get_tsType(&tcb->tcbState) ==
			    ThreadState_BlockedOnReceive) {
				/* Send and start thread running */
				cancelIPC(tcb);
				setThreadState(tcb, ThreadState_Running);
				setRegister(tcb, badgeRegister, badge);
				possibleSwitchTo(tcb);
			} else {
				/* In particular, this path is taken when a thread
				 * is waiting on a reply cap since BlockedOnReply
				 * would also trigger this path. I.e, a thread
				 * with a bound notification will not be awakened
				 * by signals on that bound notification if it is
				 * in the middle of an seL4_Call.
				 */
				ntfn_set_active(ntfnPtr, badge);
			}
		} else {
			ntfn_set_active(ntfnPtr, badge);
		}
		break;
	}
	case NtfnState_Waiting: {
		tcb_queue_t ntfn_queue;
		tcb_t *dest;
		ntfn_queue = ntfn_ptr_get_queue(ntfnPtr);
		dest = ntfn_queue.head;
		/* Haskell error "WaitingNtfn Notification must have non-empty queue" */
		/* Dequeue TCB */
		ntfn_queue = tcbEPDequeue(dest, ntfn_queue);
		ntfn_ptr_set_queue(ntfnPtr, ntfn_queue);
		/* set the thread state to idle if the queue is empty */
		if (!ntfn_queue.head) {
			notification_ptr_set_state(ntfnPtr, NtfnState_Idle);
		}
		setThreadState(dest, ThreadState_Running);
		setRegister(dest, badgeRegister, badge);
		possibleSwitchTo(dest);
		break;
	}
	case NtfnState_Active: {
		word_t badge2;
		badge2 = notification_ptr_get_ntfnMsgIdentifier(ntfnPtr);
		badge2 |= badge;
		notification_ptr_set_ntfnMsgIdentifier(ntfnPtr, badge2);
		break;
	}
	}
}
void receiveSignal(tcb_t *thread, cap_t cap, bool_t isBlocking)
{
	notification_t *ntfnPtr;
	ntfnPtr = ((notification_t *)(cap_notification_cap_get_capNtfnPtr(cap)));
	switch (notification_ptr_get_state(ntfnPtr)) {
	case NtfnState_Idle:
	case NtfnState_Waiting: {
		tcb_queue_t ntfn_queue;
		if (isBlocking) {
			/* Block thread on notification object */
			thread_state_ptr_set_tsType(&thread->tcbState,
						    ThreadState_BlockedOnNotification);
			thread_state_ptr_set_blockingObject(&thread->tcbState, ((word_t)(ntfnPtr)));
			scheduleTCB(thread);
			/* Enqueue TCB */
			ntfn_queue = ntfn_ptr_get_queue(ntfnPtr);
			ntfn_queue = tcbEPAppend(thread, ntfn_queue);
			notification_ptr_set_state(ntfnPtr, NtfnState_Waiting);
			ntfn_ptr_set_queue(ntfnPtr, ntfn_queue);
		} else {
			doNBRecvFailedTransfer(thread);
		}
		break;
	}
	case NtfnState_Active:
		setRegister(thread, badgeRegister, notification_ptr_get_ntfnMsgIdentifier(ntfnPtr));
		notification_ptr_set_state(ntfnPtr, NtfnState_Idle);
		break;
	}
}
void cancelAllSignals(notification_t *ntfnPtr)
{
	if (notification_ptr_get_state(ntfnPtr) == NtfnState_Waiting) {
		tcb_t *thread = ((tcb_t *)(notification_ptr_get_ntfnQueue_head(ntfnPtr)));
		notification_ptr_set_state(ntfnPtr, NtfnState_Idle);
		notification_ptr_set_ntfnQueue_head(ntfnPtr, 0);
		notification_ptr_set_ntfnQueue_tail(ntfnPtr, 0);
		/* Set all waiting threads to Restart */
		for (; thread; thread = thread->tcbEPNext) {
			setThreadState(thread, ThreadState_Restart);
			tcbSchedEnqueue(thread);
		}
		rescheduleRequired();
	}
}
void cancelSignal(tcb_t *threadPtr, notification_t *ntfnPtr)
{
	tcb_queue_t ntfn_queue;
	/* Haskell error "cancelSignal: notification object must be in a waiting" state */
	/* Dequeue TCB */
	ntfn_queue = ntfn_ptr_get_queue(ntfnPtr);
	ntfn_queue = tcbEPDequeue(threadPtr, ntfn_queue);
	ntfn_ptr_set_queue(ntfnPtr, ntfn_queue);
	/* Make notification object idle */
	if (!ntfn_queue.head) {
		notification_ptr_set_state(ntfnPtr, NtfnState_Idle);
	}
	/* Make thread inactive */
	setThreadState(threadPtr, ThreadState_Inactive);
}
void completeSignal(notification_t *ntfnPtr, tcb_t *tcb)
{
	word_t badge;
	if (__builtin_expect(!!(tcb && notification_ptr_get_state(ntfnPtr) == NtfnState_Active),
			     1)) {
		badge = notification_ptr_get_ntfnMsgIdentifier(ntfnPtr);
		setRegister(tcb, badgeRegister, badge);
		notification_ptr_set_state(ntfnPtr, NtfnState_Idle);
	} else {
		_fail("tried to complete signal with inactive notification object",
		      "/home/lab/projects/seL4/seL4test/kernel/src/object/notification.c", 328,
		      __func__);
	}
}
static inline void doUnbindNotification(notification_t *ntfnPtr, tcb_t *tcbptr)
{
	notification_ptr_set_ntfnBoundTCB(ntfnPtr, (word_t)0);
	tcbptr->tcbBoundNotification = NULL;
}
void unbindMaybeNotification(notification_t *ntfnPtr)
{
	tcb_t *boundTCB;
	boundTCB = (tcb_t *)notification_ptr_get_ntfnBoundTCB(ntfnPtr);
	if (boundTCB) {
		doUnbindNotification(ntfnPtr, boundTCB);
	}
}
void unbindNotification(tcb_t *tcb)
{
	notification_t *ntfnPtr;
	ntfnPtr = tcb->tcbBoundNotification;
	if (ntfnPtr) {
		doUnbindNotification(ntfnPtr, tcb);
	}
}
void bindNotification(tcb_t *tcb, notification_t *ntfnPtr)
{
	notification_ptr_set_ntfnBoundTCB(ntfnPtr, (word_t)tcb);
	tcb->tcbBoundNotification = ntfnPtr;
}
word_t getObjectSize(word_t t, word_t userObjSize)
{
	if (t >= seL4_NonArchObjectTypeCount) {
		return Arch_getObjectSize(t);
	} else {
		switch (t) {
		case seL4_TCBObject:
			return 11;
		case seL4_EndpointObject:
			return 4;
		case seL4_NotificationObject:
			return 5;
		case seL4_CapTableObject:
			return 5 + userObjSize;
		case seL4_UntypedObject:
			return userObjSize;
		default:
			_fail("Invalid object type",
			      "/home/lab/projects/seL4/seL4test/kernel/src/object/objecttype.c", 56,
			      __func__);
			return 0;
		}
	}
}
deriveCap_ret_t deriveCap(cte_t *slot, cap_t cap)
{
	deriveCap_ret_t ret;
	if (isArchCap(cap)) {
		return Arch_deriveCap(slot, cap);
	}
	switch (cap_get_capType(cap)) {
	case cap_zombie_cap:
		ret.status = EXCEPTION_NONE;
		ret.cap = cap_null_cap_new();
		break;
	case cap_irq_control_cap:
		ret.status = EXCEPTION_NONE;
		ret.cap = cap_null_cap_new();
		break;
	case cap_untyped_cap:
		ret.status = ensureNoChildren(slot);
		if (ret.status != EXCEPTION_NONE) {
			ret.cap = cap_null_cap_new();
		} else {
			ret.cap = cap;
		}
		break;
	case cap_reply_cap:
		ret.status = EXCEPTION_NONE;
		ret.cap = cap_null_cap_new();
		break;
	default:
		ret.status = EXCEPTION_NONE;
		ret.cap = cap;
	}
	return ret;
}
finaliseCap_ret_t finaliseCap(cap_t cap, bool_t final, bool_t exposed)
{
	finaliseCap_ret_t fc_ret;
	if (isArchCap(cap)) {
		return Arch_finaliseCap(cap, final);
	}
	switch (cap_get_capType(cap)) {
	case cap_endpoint_cap:
		if (final) {
			cancelAllIPC(((endpoint_t *)(cap_endpoint_cap_get_capEPPtr(cap))));
		}
		fc_ret.remainder = cap_null_cap_new();
		fc_ret.cleanupInfo = cap_null_cap_new();
		return fc_ret;
	case cap_notification_cap:
		if (final) {
			notification_t *ntfn =
				((notification_t *)(cap_notification_cap_get_capNtfnPtr(cap)));
			unbindMaybeNotification(ntfn);
			cancelAllSignals(ntfn);
		}
		fc_ret.remainder = cap_null_cap_new();
		fc_ret.cleanupInfo = cap_null_cap_new();
		return fc_ret;
	case cap_reply_cap:
	case cap_null_cap:
	case cap_domain_cap:
		fc_ret.remainder = cap_null_cap_new();
		fc_ret.cleanupInfo = cap_null_cap_new();
		return fc_ret;
	}
	if (exposed) {
		_fail("finaliseCap: failed to finalise immediately.",
		      "/home/lab/projects/seL4/seL4test/kernel/src/object/objecttype.c", 164,
		      __func__);
	}
	switch (cap_get_capType(cap)) {
	case cap_cnode_cap: {
		if (final) {
			fc_ret.remainder = Zombie_new(1ul << cap_cnode_cap_get_capCNodeRadix(cap),
						      cap_cnode_cap_get_capCNodeRadix(cap),
						      cap_cnode_cap_get_capCNodePtr(cap));
			fc_ret.cleanupInfo = cap_null_cap_new();
			return fc_ret;
		}
		break;
	}
	case cap_thread_cap: {
		if (final) {
			tcb_t *tcb;
			cte_t *cte_ptr;
			tcb = ((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap)));
			cte_ptr =
				(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) + (tcbCTable));
			unbindNotification(tcb);
			suspend(tcb);
			tcbDebugRemove(tcb);
			Arch_prepareThreadDelete(tcb);
			fc_ret.remainder =
				Zombie_new(tcbCNodeEntries, (1ul << (6)), ((word_t)(cte_ptr)));
			fc_ret.cleanupInfo = cap_null_cap_new();
			return fc_ret;
		}
		break;
	}
	case cap_zombie_cap:
		fc_ret.remainder = cap;
		fc_ret.cleanupInfo = cap_null_cap_new();
		return fc_ret;
	case cap_irq_handler_cap:
		if (final) {
			irq_t irq = (cap_irq_handler_cap_get_capIRQ(cap));
			deletingIRQHandler(irq);
			fc_ret.remainder = cap_null_cap_new();
			fc_ret.cleanupInfo = cap;
			return fc_ret;
		}
		break;
	}
	fc_ret.remainder = cap_null_cap_new();
	fc_ret.cleanupInfo = cap_null_cap_new();
	return fc_ret;
}
bool_t hasCancelSendRights(cap_t cap)
{
	switch (cap_get_capType(cap)) {
	case cap_endpoint_cap:
		return cap_endpoint_cap_get_capCanSend(cap) &&
		       cap_endpoint_cap_get_capCanReceive(cap) &&
		       cap_endpoint_cap_get_capCanGrantReply(cap) &&
		       cap_endpoint_cap_get_capCanGrant(cap);
	default:
		return false;
	}
}
bool_t sameRegionAs(cap_t cap_a, cap_t cap_b)
{
	switch (cap_get_capType(cap_a)) {
	case cap_untyped_cap:
		if (cap_get_capIsPhysical(cap_b)) {
			word_t aBase, bBase, aTop, bTop;
			aBase = (word_t)((word_t *)(cap_untyped_cap_get_capPtr(cap_a)));
			bBase = (word_t)cap_get_capPtr(cap_b);
			aTop = aBase + ((1ul << (cap_untyped_cap_get_capBlockSize(cap_a))) - 1ul);
			bTop = bBase + ((1ul << (cap_get_capSizeBits(cap_b))) - 1ul);
			return (aBase <= bBase) && (bTop <= aTop) && (bBase <= bTop);
		}
		break;
	case cap_endpoint_cap:
		if (cap_get_capType(cap_b) == cap_endpoint_cap) {
			return cap_endpoint_cap_get_capEPPtr(cap_a) ==
			       cap_endpoint_cap_get_capEPPtr(cap_b);
		}
		break;
	case cap_notification_cap:
		if (cap_get_capType(cap_b) == cap_notification_cap) {
			return cap_notification_cap_get_capNtfnPtr(cap_a) ==
			       cap_notification_cap_get_capNtfnPtr(cap_b);
		}
		break;
	case cap_cnode_cap:
		if (cap_get_capType(cap_b) == cap_cnode_cap) {
			return (cap_cnode_cap_get_capCNodePtr(cap_a) ==
				cap_cnode_cap_get_capCNodePtr(cap_b)) &&
			       (cap_cnode_cap_get_capCNodeRadix(cap_a) ==
				cap_cnode_cap_get_capCNodeRadix(cap_b));
		}
		break;
	case cap_thread_cap:
		if (cap_get_capType(cap_b) == cap_thread_cap) {
			return cap_thread_cap_get_capTCBPtr(cap_a) ==
			       cap_thread_cap_get_capTCBPtr(cap_b);
		}
		break;
	case cap_reply_cap:
		if (cap_get_capType(cap_b) == cap_reply_cap) {
			return cap_reply_cap_get_capTCBPtr(cap_a) ==
			       cap_reply_cap_get_capTCBPtr(cap_b);
		}
		break;
	case cap_domain_cap:
		if (cap_get_capType(cap_b) == cap_domain_cap) {
			return true;
		}
		break;
	case cap_irq_control_cap:
		if (cap_get_capType(cap_b) == cap_irq_control_cap ||
		    cap_get_capType(cap_b) == cap_irq_handler_cap) {
			return true;
		}
		break;
	case cap_irq_handler_cap:
		if (cap_get_capType(cap_b) == cap_irq_handler_cap) {
			return (word_t)cap_irq_handler_cap_get_capIRQ(cap_a) ==
			       (word_t)cap_irq_handler_cap_get_capIRQ(cap_b);
		}
		break;
	default:
		if (isArchCap(cap_a) && isArchCap(cap_b)) {
			return Arch_sameRegionAs(cap_a, cap_b);
		}
		break;
	}
	return false;
}
bool_t sameObjectAs(cap_t cap_a, cap_t cap_b)
{
	if (cap_get_capType(cap_a) == cap_untyped_cap) {
		return false;
	}
	if (cap_get_capType(cap_a) == cap_irq_control_cap &&
	    cap_get_capType(cap_b) == cap_irq_handler_cap) {
		return false;
	}
	if (isArchCap(cap_a) && isArchCap(cap_b)) {
		return Arch_sameObjectAs(cap_a, cap_b);
	}
	return sameRegionAs(cap_a, cap_b);
}
cap_t updateCapData(bool_t preserve, word_t newData, cap_t cap)
{
	if (isArchCap(cap)) {
		return Arch_updateCapData(preserve, newData, cap);
	}
	switch (cap_get_capType(cap)) {
	case cap_endpoint_cap:
		if (!preserve && cap_endpoint_cap_get_capEPBadge(cap) == 0) {
			return cap_endpoint_cap_set_capEPBadge(cap, newData);
		} else {
			return cap_null_cap_new();
		}
	case cap_notification_cap:
		if (!preserve && cap_notification_cap_get_capNtfnBadge(cap) == 0) {
			return cap_notification_cap_set_capNtfnBadge(cap, newData);
		} else {
			return cap_null_cap_new();
		}
	case cap_cnode_cap: {
		word_t guard, guardSize;
		seL4_CNode_CapData_t w = {.words = {newData}};
		guardSize = seL4_CNode_CapData_get_guardSize(w);
		if (guardSize + cap_cnode_cap_get_capCNodeRadix(cap) > (1 << 6)) {
			return cap_null_cap_new();
		} else {
			cap_t new_cap;
			guard = seL4_CNode_CapData_get_guard(w) & ((1ul << (guardSize)) - 1ul);
			new_cap = cap_cnode_cap_set_capCNodeGuard(cap, guard);
			new_cap = cap_cnode_cap_set_capCNodeGuardSize(new_cap, guardSize);
			return new_cap;
		}
	}
	default:
		return cap;
	}
}
cap_t maskCapRights(seL4_CapRights_t cap_rights, cap_t cap)
{
	if (isArchCap(cap)) {
		return Arch_maskCapRights(cap_rights, cap);
	}
	switch (cap_get_capType(cap)) {
	case cap_null_cap:
	case cap_domain_cap:
	case cap_cnode_cap:
	case cap_untyped_cap:
	case cap_irq_control_cap:
	case cap_irq_handler_cap:
	case cap_zombie_cap:
	case cap_thread_cap:
		return cap;
	case cap_endpoint_cap: {
		cap_t new_cap;
		new_cap = cap_endpoint_cap_set_capCanSend(
			cap, cap_endpoint_cap_get_capCanSend(cap) &
				     seL4_CapRights_get_capAllowWrite(cap_rights));
		new_cap = cap_endpoint_cap_set_capCanReceive(
			new_cap, cap_endpoint_cap_get_capCanReceive(cap) &
					 seL4_CapRights_get_capAllowRead(cap_rights));
		new_cap = cap_endpoint_cap_set_capCanGrant(
			new_cap, cap_endpoint_cap_get_capCanGrant(cap) &
					 seL4_CapRights_get_capAllowGrant(cap_rights));
		new_cap = cap_endpoint_cap_set_capCanGrantReply(
			new_cap, cap_endpoint_cap_get_capCanGrantReply(cap) &
					 seL4_CapRights_get_capAllowGrantReply(cap_rights));
		return new_cap;
	}
	case cap_notification_cap: {
		cap_t new_cap;
		new_cap = cap_notification_cap_set_capNtfnCanSend(
			cap, cap_notification_cap_get_capNtfnCanSend(cap) &
				     seL4_CapRights_get_capAllowWrite(cap_rights));
		new_cap = cap_notification_cap_set_capNtfnCanReceive(
			new_cap, cap_notification_cap_get_capNtfnCanReceive(cap) &
					 seL4_CapRights_get_capAllowRead(cap_rights));
		return new_cap;
	}
	case cap_reply_cap: {
		cap_t new_cap;
		new_cap = cap_reply_cap_set_capReplyCanGrant(
			cap, cap_reply_cap_get_capReplyCanGrant(cap) &
				     seL4_CapRights_get_capAllowGrant(cap_rights));
		return new_cap;
	}
	default:
		_fail("Invalid cap type",
		      "/home/lab/projects/seL4/seL4test/kernel/src/object/objecttype.c", 506,
		      __func__); /* Sentinel for invalid enums */
	}
}
cap_t createObject(object_t t, void *regionBase, word_t userSize, bool_t deviceMemory)
{
	/* Handle architecture-specific objects. */
	if (t >= (object_t)seL4_NonArchObjectTypeCount) {
		return Arch_createObject(t, regionBase, userSize, deviceMemory);
	}
	/* Create objects. */
	switch ((api_object_t)t) {
	case seL4_TCBObject: {
		tcb_t *tcb;
		tcb = ((tcb_t *)((word_t)regionBase + (1ul << ((11 - 1)))));
		/** AUXUPD: "(True, ptr_retyps 1
		  (Ptr ((ptr_val \<acute>tcb) - ctcb_offset) :: (cte_C[5]) ptr)
		    o (ptr_retyp \<acute>tcb))" */
		/* Setup non-zero parts of the TCB. */
		Arch_initContext(&tcb->tcbArch.tcbContext);
		tcb->tcbTimeSlice = 5;
		tcb->tcbDomain = ksCurDomain;
		/* Initialize the new TCB to the current core */
		strlcpy(((debug_tcb_t *)(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) +
					 (tcbCNodeEntries)))
				->tcbName,
			"child of: '",
			((1ul << (11 - 1)) - (tcbCNodeEntries * sizeof(cte_t)) -
			 sizeof(debug_tcb_t)));
		strlcat(((debug_tcb_t *)(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) +
					 (tcbCNodeEntries)))
				->tcbName,
			((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
						    ~((1ul << (11)) - 1ul))) +
					 (tcbCNodeEntries)))
				->tcbName,
			((1ul << (11 - 1)) - (tcbCNodeEntries * sizeof(cte_t)) -
			 sizeof(debug_tcb_t)));
		strlcat(((debug_tcb_t *)(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) +
					 (tcbCNodeEntries)))
				->tcbName,
			"'",
			((1ul << (11 - 1)) - (tcbCNodeEntries * sizeof(cte_t)) -
			 sizeof(debug_tcb_t)));
		tcbDebugAppend(tcb);
		return cap_thread_cap_new(((word_t)(tcb)));
	}
	case seL4_EndpointObject:
		/** AUXUPD: "(True, ptr_retyp
		  (Ptr (ptr_val \<acute>regionBase) :: endpoint_C ptr))" */
		return cap_endpoint_cap_new(0, true, true, true, true, ((word_t)(regionBase)));
	case seL4_NotificationObject:
		/** AUXUPD: "(True, ptr_retyp
		      (Ptr (ptr_val \<acute>regionBase) :: notification_C ptr))" */
		return cap_notification_cap_new(0, true, true, ((word_t)(regionBase)));
	case seL4_CapTableObject:
		/** AUXUPD: "(True, ptr_arr_retyps (2 ^ (unat \<acute>userSize))
		  (Ptr (ptr_val \<acute>regionBase) :: cte_C ptr))" */
		/** GHOSTUPD: "(True, gs_new_cnodes (unat \<acute>userSize)
					(ptr_val \<acute>regionBase)
					(4 + unat \<acute>userSize))" */
		return cap_cnode_cap_new(userSize, 0, 0, ((word_t)(regionBase)));
	case seL4_UntypedObject:
		/*
		 * No objects need to be created; instead, just insert caps into
		 * the destination slots.
		 */
		return cap_untyped_cap_new(0, !!deviceMemory, userSize, ((word_t)(regionBase)));
	default:
		_fail("Invalid object type",
		      "/home/lab/projects/seL4/seL4test/kernel/src/object/objecttype.c", 585,
		      __func__);
	}
}
void createNewObjects(object_t t, cte_t *parent, cte_t *destCNode, word_t destOffset,
		      word_t destLength, void *regionBase, word_t userSize, bool_t deviceMemory)
{
	word_t objectSize;
	void *nextFreeArea;
	word_t i;
	word_t totalObjectSize;
	/* ghost check that we're visiting less bytes than the max object size */
	objectSize = getObjectSize(t, userSize);
	totalObjectSize = destLength << objectSize;
	/** GHOSTUPD: "(gs_get_assn cap_get_capSizeBits_'proc \<acute>ghost'state = 0
	    \<or> \<acute>totalObjectSize <= gs_get_assn cap_get_capSizeBits_'proc
	   \<acute>ghost'state, id)" */
	/* Create the objects. */
	nextFreeArea = regionBase;
	for (i = 0; i < destLength; i++) {
		/* Create the object. */
		/** AUXUPD: "(True, typ_region_bytes (ptr_val \<acute> nextFreeArea + ((\<acute> i)
		 * << unat (\<acute> objectSize))) (unat (\<acute> objectSize)))" */
		cap_t cap = createObject(t, (void *)((word_t)nextFreeArea + (i << objectSize)),
					 userSize, deviceMemory);
		/* Insert the cap into the user's cspace. */
		insertNewCap(parent, &destCNode[destOffset + i], cap);
		/* Move along to the next region of memory. been merged into a formula of i */
	}
}
exception_t decodeInvocation(word_t invLabel, word_t length, cptr_t capIndex, cte_t *slot,
			     cap_t cap, bool_t block, bool_t call, word_t *buffer)
{
	if (isArchCap(cap)) {
		return Arch_decodeInvocation(invLabel, length, capIndex, slot, cap, call, buffer);
	}
	switch (cap_get_capType(cap)) {
	case cap_null_cap:
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Attempted to invoke a "
			       "null cap #%lu.>>\n",
			       0lu, __func__, 637, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), capIndex);
		} while (0);
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 0;
		return EXCEPTION_SYSCALL_ERROR;
	case cap_zombie_cap:
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Attempted to invoke a "
			       "zombie cap #%lu.>>\n",
			       0lu, __func__, 643, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), capIndex);
		} while (0);
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 0;
		return EXCEPTION_SYSCALL_ERROR;
	case cap_endpoint_cap:
		if (!cap_endpoint_cap_get_capCanSend(cap)) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Attempted to "
				       "invoke a read-only endpoint cap #%lu.>>\n",
				       0lu, __func__, 650, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread), capIndex);
			} while (0);
			current_syscall_error.type = seL4_InvalidCapability;
			current_syscall_error.invalidCapNumber = 0;
			return EXCEPTION_SYSCALL_ERROR;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return performInvocation_Endpoint(
			((endpoint_t *)(cap_endpoint_cap_get_capEPPtr(cap))),
			cap_endpoint_cap_get_capEPBadge(cap), cap_endpoint_cap_get_capCanGrant(cap),
			cap_endpoint_cap_get_capCanGrantReply(cap), block, call);
	case cap_notification_cap: {
		if (!cap_notification_cap_get_capNtfnCanSend(cap)) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Attempted to "
				       "invoke a read-only notification cap #%lu.>>\n",
				       0lu, __func__, 674, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread), capIndex);
			} while (0);
			current_syscall_error.type = seL4_InvalidCapability;
			current_syscall_error.invalidCapNumber = 0;
			return EXCEPTION_SYSCALL_ERROR;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return performInvocation_Notification(
			((notification_t *)(cap_notification_cap_get_capNtfnPtr(cap))),
			cap_notification_cap_get_capNtfnBadge(cap));
	}
	case cap_reply_cap:
		if (cap_reply_cap_get_capReplyMaster(cap)) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Attempted to "
				       "invoke an invalid reply cap #%lu.>>\n",
				       0lu, __func__, 697, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread), capIndex);
			} while (0);
			current_syscall_error.type = seL4_InvalidCapability;
			current_syscall_error.invalidCapNumber = 0;
			return EXCEPTION_SYSCALL_ERROR;
		}
		setThreadState(ksCurThread, ThreadState_Restart);
		return performInvocation_Reply(((tcb_t *)(cap_reply_cap_get_capTCBPtr(cap))), slot,
					       cap_reply_cap_get_capReplyCanGrant(cap));
	case cap_thread_cap:
		return decodeTCBInvocation(invLabel, length, cap, slot, call, buffer);
	case cap_domain_cap:
		return decodeDomainInvocation(invLabel, length, buffer);
	case cap_cnode_cap:
		return decodeCNodeInvocation(invLabel, length, cap, buffer);
	case cap_untyped_cap:
		return decodeUntypedInvocation(invLabel, length, slot, cap, call, buffer);
	case cap_irq_control_cap:
		return decodeIRQControlInvocation(invLabel, length, slot, buffer);
	case cap_irq_handler_cap:
		return decodeIRQHandlerInvocation(invLabel, (cap_irq_handler_cap_get_capIRQ(cap)));
	default:
		_fail("Invalid cap type",
		      "/home/lab/projects/seL4/seL4test/kernel/src/object/objecttype.c", 774,
		      __func__);
	}
}
exception_t performInvocation_Endpoint(endpoint_t *ep, word_t badge, bool_t canGrant,
				       bool_t canGrantReply, bool_t block, bool_t call)
{
	sendIPC(block, call, badge, canGrant, canGrantReply, ksCurThread, ep);
	return EXCEPTION_NONE;
}
exception_t performInvocation_Notification(notification_t *ntfn, word_t badge)
{
	sendSignal(ntfn, badge);
	return EXCEPTION_NONE;
}
exception_t performInvocation_Reply(tcb_t *thread, cte_t *slot, bool_t canGrant)
{
	doReplyTransfer(ksCurThread, thread, slot, canGrant);
	return EXCEPTION_NONE;
}
word_t cap_get_capSizeBits(cap_t cap)
{
	cap_tag_t ctag;
	ctag = cap_get_capType(cap);
	switch (ctag) {
	case cap_untyped_cap:
		return cap_untyped_cap_get_capBlockSize(cap);
	case cap_endpoint_cap:
		return 4;
	case cap_notification_cap:
		return 5;
	case cap_cnode_cap:
		return cap_cnode_cap_get_capCNodeRadix(cap) + 5;
	case cap_thread_cap:
		return 11;
	case cap_zombie_cap: {
		word_t type = cap_zombie_cap_get_capZombieType(cap);
		if (type == (1ul << (6))) {
			return 11;
		}
		return ((type) & ((1ul << (6)) - 1ul)) + 5;
	}
	case cap_null_cap:
		return 0;
	case cap_domain_cap:
		return 0;
	case cap_reply_cap:
		return 0;
	case cap_irq_control_cap:
		return 0;
	case cap_irq_handler_cap:
		return 0;
	default:
		return cap_get_archCapSizeBits(cap);
	}
}
/* Returns whether or not this capability has memory associated
 * with it or not. Referring to this as 'being physical' is to
 * match up with the Haskell and abstract specifications */
bool_t cap_get_capIsPhysical(cap_t cap)
{
	cap_tag_t ctag;
	ctag = cap_get_capType(cap);
	switch (ctag) {
	case cap_untyped_cap:
		return true;
	case cap_endpoint_cap:
		return true;
	case cap_notification_cap:
		return true;
	case cap_cnode_cap:
		return true;
	case cap_thread_cap:
		return true;
	case cap_zombie_cap:
		return true;
	case cap_domain_cap:
		return false;
	case cap_reply_cap:
		return false;
	case cap_irq_control_cap:
		return false;
	case cap_irq_handler_cap:
		return false;
	default:
		return cap_get_archCapIsPhysical(cap);
	}
}
void *cap_get_capPtr(cap_t cap)
{
	cap_tag_t ctag;
	ctag = cap_get_capType(cap);
	switch (ctag) {
	case cap_untyped_cap:
		return ((word_t *)(cap_untyped_cap_get_capPtr(cap)));
	case cap_endpoint_cap:
		return ((endpoint_t *)(cap_endpoint_cap_get_capEPPtr(cap)));
	case cap_notification_cap:
		return ((notification_t *)(cap_notification_cap_get_capNtfnPtr(cap)));
	case cap_cnode_cap:
		return ((cte_t *)(cap_cnode_cap_get_capCNodePtr(cap)));
	case cap_thread_cap:
		return (((cte_t *)((word_t)(cap_thread_cap_get_capTCBPtr(cap)) &
				   ~((1ul << (11)) - 1ul))) +
			(0));
	case cap_zombie_cap:
		return ((cte_t *)(cap_zombie_cap_get_capZombiePtr(cap)));
	case cap_domain_cap:
		return NULL;
	case cap_reply_cap:
		return NULL;
	case cap_irq_control_cap:
		return NULL;
	case cap_irq_handler_cap:
		return NULL;
	default:
		return cap_get_archCapPtr(cap);
	}
}
bool_t isCapRevocable(cap_t derivedCap, cap_t srcCap)
{
	if (isArchCap(derivedCap)) {
		return Arch_isCapRevocable(derivedCap, srcCap);
	}
	switch (cap_get_capType(derivedCap)) {
	case cap_endpoint_cap:
		return (cap_endpoint_cap_get_capEPBadge(derivedCap) !=
			cap_endpoint_cap_get_capEPBadge(srcCap));
	case cap_notification_cap:
		return (cap_notification_cap_get_capNtfnBadge(derivedCap) !=
			cap_notification_cap_get_capNtfnBadge(srcCap));
	case cap_irq_handler_cap:
		return (cap_get_capType(srcCap) == cap_irq_control_cap);
	case cap_untyped_cap:
		return true;
	default:
		return false;
	}
}
static exception_t checkPrio(prio_t prio, tcb_t *auth)
{
	prio_t mcp;
	mcp = auth->tcbMCP;
	/* system invariant: existing MCPs are bounded */
	/* can't assign a priority greater than our own mcp */
	if (prio > mcp) {
		current_syscall_error.type = seL4_RangeError;
		current_syscall_error.rangeErrorMin = seL4_MinPrio;
		current_syscall_error.rangeErrorMax = mcp;
		return EXCEPTION_SYSCALL_ERROR;
	}
	return EXCEPTION_NONE;
}
static inline void addToBitmap(word_t cpu, word_t dom, word_t prio)
{
	word_t l1index;
	word_t l1index_inverted;
	l1index = prio_to_l1index(prio);
	l1index_inverted = invert_l1index(l1index);
	ksReadyQueuesL1Bitmap[dom] |= (1ul << (l1index));
	/* we invert the l1 index when accessed the 2nd level of the bitmap in
	   order to increase the liklihood that high prio threads l2 index word will
	   be on the same cache line as the l1 index word - this makes sure the
	   fastpath is fastest for high prio threads */
	ksReadyQueuesL2Bitmap[dom][l1index_inverted] |= (1ul << (prio & ((1ul << (6)) - 1ul)));
}
static inline void removeFromBitmap(word_t cpu, word_t dom, word_t prio)
{
	word_t l1index;
	word_t l1index_inverted;
	l1index = prio_to_l1index(prio);
	l1index_inverted = invert_l1index(l1index);
	ksReadyQueuesL2Bitmap[dom][l1index_inverted] &= ~(1ul << (prio & ((1ul << (6)) - 1ul)));
	if (__builtin_expect(!!(!ksReadyQueuesL2Bitmap[dom][l1index_inverted]), 0)) {
		ksReadyQueuesL1Bitmap[dom] &= ~(1ul << (l1index));
	}
}
/* Add TCB to the head of a scheduler queue */
void tcbSchedEnqueue(tcb_t *tcb)
{
	if (!thread_state_get_tcbQueued(tcb->tcbState)) {
		tcb_queue_t queue;
		dom_t dom;
		prio_t prio;
		word_t idx;
		dom = tcb->tcbDomain;
		prio = tcb->tcbPriority;
		idx = ready_queues_index(dom, prio);
		queue = ksReadyQueues[idx];
		if (!queue.end) { /* Empty list */
			queue.end = tcb;
			addToBitmap(0, dom, prio);
		} else {
			queue.head->tcbSchedPrev = tcb;
		}
		tcb->tcbSchedPrev = NULL;
		tcb->tcbSchedNext = queue.head;
		queue.head = tcb;
		ksReadyQueues[idx] = queue;
		thread_state_ptr_set_tcbQueued(&tcb->tcbState, true);
	}
}
/* Add TCB to the end of a scheduler queue */
void tcbSchedAppend(tcb_t *tcb)
{
	if (!thread_state_get_tcbQueued(tcb->tcbState)) {
		tcb_queue_t queue;
		dom_t dom;
		prio_t prio;
		word_t idx;
		dom = tcb->tcbDomain;
		prio = tcb->tcbPriority;
		idx = ready_queues_index(dom, prio);
		queue = ksReadyQueues[idx];
		if (!queue.head) { /* Empty list */
			queue.head = tcb;
			addToBitmap(0, dom, prio);
		} else {
			queue.end->tcbSchedNext = tcb;
		}
		tcb->tcbSchedPrev = queue.end;
		tcb->tcbSchedNext = NULL;
		queue.end = tcb;
		ksReadyQueues[idx] = queue;
		thread_state_ptr_set_tcbQueued(&tcb->tcbState, true);
	}
}
/* Remove TCB from a scheduler queue */
void tcbSchedDequeue(tcb_t *tcb)
{
	if (thread_state_get_tcbQueued(tcb->tcbState)) {
		tcb_queue_t queue;
		dom_t dom;
		prio_t prio;
		word_t idx;
		dom = tcb->tcbDomain;
		prio = tcb->tcbPriority;
		idx = ready_queues_index(dom, prio);
		queue = ksReadyQueues[idx];
		if (tcb->tcbSchedPrev) {
			tcb->tcbSchedPrev->tcbSchedNext = tcb->tcbSchedNext;
		} else {
			queue.head = tcb->tcbSchedNext;
			if (__builtin_expect(!!(!tcb->tcbSchedNext), 1)) {
				removeFromBitmap(0, dom, prio);
			}
		}
		if (tcb->tcbSchedNext) {
			tcb->tcbSchedNext->tcbSchedPrev = tcb->tcbSchedPrev;
		} else {
			queue.end = tcb->tcbSchedPrev;
		}
		ksReadyQueues[idx] = queue;
		thread_state_ptr_set_tcbQueued(&tcb->tcbState, false);
	}
}
void tcbDebugAppend(tcb_t *tcb)
{
	debug_tcb_t *debug_tcb =
		((debug_tcb_t *)(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) +
				 (tcbCNodeEntries)));
	/* prepend to the list */
	debug_tcb->tcbDebugPrev = NULL;
	debug_tcb->tcbDebugNext = ksDebugTCBs;
	if (ksDebugTCBs) {
		((debug_tcb_t *)(((cte_t *)((word_t)(ksDebugTCBs) & ~((1ul << (11)) - 1ul))) +
				 (tcbCNodeEntries)))
			->tcbDebugPrev = tcb;
	}
	ksDebugTCBs = tcb;
}
void tcbDebugRemove(tcb_t *tcb)
{
	debug_tcb_t *debug_tcb =
		((debug_tcb_t *)(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) +
				 (tcbCNodeEntries)));
	if (tcb == ksDebugTCBs) {
		ksDebugTCBs = ((debug_tcb_t *)(((cte_t *)((word_t)(ksDebugTCBs) &
							  ~((1ul << (11)) - 1ul))) +
					       (tcbCNodeEntries)))
				      ->tcbDebugNext;
	} else {
		((debug_tcb_t *)(((cte_t *)((word_t)(debug_tcb->tcbDebugPrev) &
					    ~((1ul << (11)) - 1ul))) +
				 (tcbCNodeEntries)))
			->tcbDebugNext = debug_tcb->tcbDebugNext;
	}
	if (debug_tcb->tcbDebugNext) {
		((debug_tcb_t *)(((cte_t *)((word_t)(debug_tcb->tcbDebugNext) &
					    ~((1ul << (11)) - 1ul))) +
				 (tcbCNodeEntries)))
			->tcbDebugPrev = debug_tcb->tcbDebugPrev;
	}
	debug_tcb->tcbDebugPrev = NULL;
	debug_tcb->tcbDebugNext = NULL;
}
/* Add TCB to the end of an endpoint queue */
tcb_queue_t tcbEPAppend(tcb_t *tcb, tcb_queue_t queue)
{
	if (!queue.head) { /* Empty list */
		queue.head = tcb;
	} else {
		queue.end->tcbEPNext = tcb;
	}
	tcb->tcbEPPrev = queue.end;
	tcb->tcbEPNext = NULL;
	queue.end = tcb;
	return queue;
}
/* Remove TCB from an endpoint queue */
tcb_queue_t tcbEPDequeue(tcb_t *tcb, tcb_queue_t queue)
{
	if (tcb->tcbEPPrev) {
		tcb->tcbEPPrev->tcbEPNext = tcb->tcbEPNext;
	} else {
		queue.head = tcb->tcbEPNext;
	}
	if (tcb->tcbEPNext) {
		tcb->tcbEPNext->tcbEPPrev = tcb->tcbEPPrev;
	} else {
		queue.end = tcb->tcbEPPrev;
	}
	return queue;
}
cptr_t getExtraCPtr(word_t *bufferPtr, word_t i)
{
	return (cptr_t)bufferPtr[seL4_MsgMaxLength + 2 + i];
}
void setExtraBadge(word_t *bufferPtr, word_t badge, word_t i)
{
	bufferPtr[seL4_MsgMaxLength + 2 + i] = badge;
}
void setupCallerCap(tcb_t *sender, tcb_t *receiver, bool_t canGrant)
{
	cte_t *replySlot, *callerSlot;
	cap_t masterCap, callerCap;
	setThreadState(sender, ThreadState_BlockedOnReply);
	replySlot = (((cte_t *)((word_t)(sender) & ~((1ul << (11)) - 1ul))) + (tcbReply));
	masterCap = replySlot->cap;
	/* Haskell error: "Sender must have a valid master reply cap" */
	callerSlot = (((cte_t *)((word_t)(receiver) & ~((1ul << (11)) - 1ul))) + (tcbCaller));
	callerCap = callerSlot->cap;
	/* Haskell error: "Caller cap must not already exist" */
	cteInsert(cap_reply_cap_new(canGrant, false, ((word_t)(sender))), replySlot, callerSlot);
}
void deleteCallerCap(tcb_t *receiver)
{
	cte_t *callerSlot;
	callerSlot = (((cte_t *)((word_t)(receiver) & ~((1ul << (11)) - 1ul))) + (tcbCaller));
	/** GHOSTUPD: "(True, gs_set_assn cteDeleteOne_'proc (ucast cap_reply_cap))" */
	cteDeleteOne(callerSlot);
}
extra_caps_t current_extra_caps;
exception_t lookupExtraCaps(tcb_t *thread, word_t *bufferPtr, seL4_MessageInfo_t info)
{
	lookupSlot_raw_ret_t lu_ret;
	cptr_t cptr;
	word_t i, length;
	if (!bufferPtr) {
		current_extra_caps.excaprefs[0] = NULL;
		return EXCEPTION_NONE;
	}
	length = seL4_MessageInfo_get_extraCaps(info);
	for (i = 0; i < length; i++) {
		cptr = getExtraCPtr(bufferPtr, i);
		lu_ret = lookupSlot(thread, cptr);
		if (lu_ret.status != EXCEPTION_NONE) {
			current_fault = seL4_Fault_CapFault_new(cptr, false);
			return lu_ret.status;
		}
		current_extra_caps.excaprefs[i] = lu_ret.slot;
	}
	if (i < ((1ul << (seL4_MsgExtraCapBits)) - 1)) {
		current_extra_caps.excaprefs[i] = NULL;
	}
	return EXCEPTION_NONE;
}
/* Copy IPC MRs from one thread to another */
word_t copyMRs(tcb_t *sender, word_t *sendBuf, tcb_t *receiver, word_t *recvBuf, word_t n)
{
	word_t i;
	/* Copy inline words */
	for (i = 0; i < n && i < n_msgRegisters; i++) {
		setRegister(receiver, msgRegisters[i], getRegister(sender, msgRegisters[i]));
	}
	if (!recvBuf || !sendBuf) {
		return i;
	}
	/* Copy out-of-line words */
	for (; i < n; i++) {
		recvBuf[i + 1] = sendBuf[i + 1];
	}
	return i;
}
static exception_t invokeSetTLSBase(tcb_t *thread, word_t tls_base)
{
	setRegister(thread, TLS_BASE, tls_base);
	if (thread == ksCurThread) {
		/* If this is the current thread force a reschedule to ensure that any changes
		 * to the TLS_BASE are realized */
		rescheduleRequired();
	}
	return EXCEPTION_NONE;
}
static exception_t decodeSetTLSBase(cap_t cap, word_t length, word_t *buffer)
{
	word_t tls_base;
	if (length < 1) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetTLSBase: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 763, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	tls_base = getSyscallArg(0, buffer);
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeSetTLSBase(((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap))), tls_base);
}
/* The following functions sit in the syscall error monad, but include the
 * exception cases for the preemptible bottom end, as they call the invoke
 * functions directly.  This is a significant deviation from the Haskell
 * spec. */
exception_t decodeTCBInvocation(word_t invLabel, word_t length, cap_t cap, cte_t *slot, bool_t call,
				word_t *buffer)
{
	/* Stall the core if we are operating on a remote TCB that is currently running */
	switch (invLabel) {
	case TCBReadRegisters:
		/* Second level of decoding */
		return decodeReadRegisters(cap, length, call, buffer);
	case TCBWriteRegisters:
		return decodeWriteRegisters(cap, length, buffer);
	case TCBCopyRegisters:
		return decodeCopyRegisters(cap, length, buffer);
	case TCBSuspend:
		/* Jump straight to the invoke */
		setThreadState(ksCurThread, ThreadState_Restart);
		return invokeTCB_Suspend(((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap))));
	case TCBResume:
		setThreadState(ksCurThread, ThreadState_Restart);
		return invokeTCB_Resume(((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap))));
	case TCBConfigure:
		return decodeTCBConfigure(cap, length, slot, buffer);
	case TCBSetPriority:
		return decodeSetPriority(cap, length, buffer);
	case TCBSetMCPriority:
		return decodeSetMCPriority(cap, length, buffer);
	case TCBSetSchedParams:
		return decodeSetSchedParams(cap, length, buffer);
	case TCBSetIPCBuffer:
		return decodeSetIPCBuffer(cap, length, slot, buffer);
	case TCBSetSpace:
		return decodeSetSpace(cap, length, slot, buffer);
	case TCBBindNotification:
		return decodeBindNotification(cap);
	case TCBUnbindNotification:
		return decodeUnbindNotification(cap);
		/* There is no notion of arch specific TCB invocations so this needs to go here */
	case TCBSetTLSBase:
		return decodeSetTLSBase(cap, length, buffer);
	default:
		/* Haskell: "throw IllegalOperation" */
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB: Illegal operation."
			       ">>"
			       "\n",
			       0lu, __func__, 869, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
}
enum CopyRegistersFlags {
	CopyRegisters_suspendSource = 0,
	CopyRegisters_resumeTarget = 1,
	CopyRegisters_transferFrame = 2,
	CopyRegisters_transferInteger = 3
};
exception_t decodeCopyRegisters(cap_t cap, word_t length, word_t *buffer)
{
	word_t transferArch;
	tcb_t *srcTCB;
	cap_t source_cap;
	word_t flags;
	if (length < 1 || current_extra_caps.excaprefs[0] == NULL) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB CopyRegisters: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 890, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	flags = getSyscallArg(0, buffer);
	transferArch = Arch_decodeTransfer(flags >> 8);
	source_cap = current_extra_caps.excaprefs[0]->cap;
	if (cap_get_capType(source_cap) == cap_thread_cap) {
		srcTCB = ((tcb_t *)(cap_thread_cap_get_capTCBPtr(source_cap)));
	} else {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB CopyRegisters: Invalid source TCB."
			       ">>"
			       "\n",
			       0lu, __func__, 904, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeTCB_CopyRegisters(((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap))), srcTCB,
				       flags & (1ul << (CopyRegisters_suspendSource)),
				       flags & (1ul << (CopyRegisters_resumeTarget)),
				       flags & (1ul << (CopyRegisters_transferFrame)),
				       flags & (1ul << (CopyRegisters_transferInteger)),
				       transferArch);
}
enum ReadRegistersFlags { ReadRegisters_suspend = 0 };
exception_t decodeReadRegisters(cap_t cap, word_t length, bool_t call, word_t *buffer)
{
	word_t transferArch, flags, n;
	tcb_t *thread;
	if (length < 2) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB ReadRegisters: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 932, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	flags = getSyscallArg(0, buffer);
	n = getSyscallArg(1, buffer);
	if (n < 1 || n > n_frameRegisters + n_gpRegisters) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB ReadRegisters: Attempted to read an invalid number of "
			       "registers (%d)."
			       ">>"
			       "\n",
			       0lu, __func__, 941, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), (int)n);
		} while (0);
		current_syscall_error.type = seL4_RangeError;
		current_syscall_error.rangeErrorMin = 1;
		current_syscall_error.rangeErrorMax = n_frameRegisters + n_gpRegisters;
		return EXCEPTION_SYSCALL_ERROR;
	}
	transferArch = Arch_decodeTransfer(flags >> 8);
	thread = ((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap)));
	if (thread == ksCurThread) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB ReadRegisters: Attempted to read our own registers."
			       ">>"
			       "\n",
			       0lu, __func__, 954, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeTCB_ReadRegisters(((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap))),
				       flags & (1ul << (ReadRegisters_suspend)), n, transferArch,
				       call);
}
enum WriteRegistersFlags { WriteRegisters_resume = 0 };
exception_t decodeWriteRegisters(cap_t cap, word_t length, word_t *buffer)
{
	word_t flags, w;
	word_t transferArch;
	tcb_t *thread;
	if (length < 2) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB WriteRegisters: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 977, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	flags = getSyscallArg(0, buffer);
	w = getSyscallArg(1, buffer);
	if (length - 2 < w) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB WriteRegisters: Message too short for requested write size "
			       "(%d/%d)."
			       ">>"
			       "\n",
			       0lu, __func__, 986, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), (int)(length - 2), (int)w);
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	transferArch = Arch_decodeTransfer(flags >> 8);
	thread = ((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap)));
	if (thread == ksCurThread) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB WriteRegisters: Attempted to write our own registers."
			       ">>"
			       "\n",
			       0lu, __func__, 996, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeTCB_WriteRegisters(thread, flags & (1ul << (WriteRegisters_resume)), w,
					transferArch, buffer);
}
/* TCBConfigure batches SetIPCBuffer and parts of SetSpace. */
exception_t decodeTCBConfigure(cap_t cap, word_t length, cte_t *slot, word_t *buffer)
{
	cte_t *bufferSlot, *cRootSlot, *vRootSlot;
	cap_t bufferCap, cRootCap, vRootCap;
	deriveCap_ret_t dc_ret;
	word_t cRootData, vRootData, bufferAddr;
	if (length < 4 || current_extra_caps.excaprefs[0] == NULL ||
	    current_extra_caps.excaprefs[1] == NULL || current_extra_caps.excaprefs[2] == NULL) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB Configure: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 1045, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	cptr_t faultEP = getSyscallArg(0, buffer);
	cRootData = getSyscallArg(1, buffer);
	vRootData = getSyscallArg(2, buffer);
	bufferAddr = getSyscallArg(3, buffer);
	cRootSlot = current_extra_caps.excaprefs[0];
	cRootCap = current_extra_caps.excaprefs[0]->cap;
	vRootSlot = current_extra_caps.excaprefs[1];
	vRootCap = current_extra_caps.excaprefs[1]->cap;
	bufferSlot = current_extra_caps.excaprefs[2];
	bufferCap = current_extra_caps.excaprefs[2]->cap;
	if (bufferAddr == 0) {
		bufferSlot = NULL;
	} else {
		dc_ret = deriveCap(bufferSlot, bufferCap);
		if (dc_ret.status != EXCEPTION_NONE) {
			return dc_ret.status;
		}
		bufferCap = dc_ret.cap;
		exception_t e = checkValidIPCBuffer(bufferAddr, bufferCap);
		if (e != EXCEPTION_NONE) {
			return e;
		}
	}
	if (slotCapLongRunningDelete((((cte_t *)((word_t)(cap_thread_cap_get_capTCBPtr(cap)) &
						 ~((1ul << (11)) - 1ul))) +
				      (tcbCTable))) ||
	    slotCapLongRunningDelete((((cte_t *)((word_t)(cap_thread_cap_get_capTCBPtr(cap)) &
						 ~((1ul << (11)) - 1ul))) +
				      (tcbVTable)))) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB Configure: CSpace or VSpace currently being deleted."
			       ">>"
			       "\n",
			       0lu, __func__, 1087, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (cRootData != 0) {
		cRootCap = updateCapData(false, cRootData, cRootCap);
	}
	dc_ret = deriveCap(cRootSlot, cRootCap);
	if (dc_ret.status != EXCEPTION_NONE) {
		return dc_ret.status;
	}
	cRootCap = dc_ret.cap;
	if (cap_get_capType(cRootCap) != cap_cnode_cap) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB Configure: CSpace cap is invalid."
			       ">>"
			       "\n",
			       0lu, __func__, 1103, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (vRootData != 0) {
		vRootCap = updateCapData(false, vRootData, vRootCap);
	}
	dc_ret = deriveCap(vRootSlot, vRootCap);
	if (dc_ret.status != EXCEPTION_NONE) {
		return dc_ret.status;
	}
	vRootCap = dc_ret.cap;
	if (!isValidVTableRoot(vRootCap)) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB Configure: VSpace cap is invalid."
			       ">>"
			       "\n",
			       0lu, __func__, 1119, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeTCB_ThreadControl(
		((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap))), slot, faultEP, 0, 0, cRootCap,
		cRootSlot, vRootCap, vRootSlot, bufferAddr, bufferCap, bufferSlot,
		thread_control_update_space | thread_control_update_ipc_buffer);
}
exception_t decodeSetPriority(cap_t cap, word_t length, word_t *buffer)
{
	if (length < 1 || current_extra_caps.excaprefs[0] == NULL) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetPriority: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 1150, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	prio_t newPrio = getSyscallArg(0, buffer);
	cap_t authCap = current_extra_caps.excaprefs[0]->cap;
	if (cap_get_capType(authCap) != cap_thread_cap) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "Set priority: authority cap not a TCB."
			       ">>"
			       "\n",
			       0lu, __func__, 1159, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	tcb_t *authTCB = ((tcb_t *)(cap_thread_cap_get_capTCBPtr(authCap)));
	exception_t status = checkPrio(newPrio, authTCB);
	if (status != EXCEPTION_NONE) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetPriority: Requested priority %lu too high (max %lu)."
			       ">>"
			       "\n",
			       0lu, __func__, 1168, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), (unsigned long)newPrio,
			       (unsigned long)authTCB->tcbMCP);
		} while (0);
		return status;
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeTCB_ThreadControl(((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap))), NULL, 0, 0,
				       newPrio, cap_null_cap_new(), NULL, cap_null_cap_new(), NULL,
				       0, cap_null_cap_new(), NULL, thread_control_update_priority);
}
exception_t decodeSetMCPriority(cap_t cap, word_t length, word_t *buffer)
{
	if (length < 1 || current_extra_caps.excaprefs[0] == NULL) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetMCPriority: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 1194, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	prio_t newMcp = getSyscallArg(0, buffer);
	cap_t authCap = current_extra_caps.excaprefs[0]->cap;
	if (cap_get_capType(authCap) != cap_thread_cap) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetMCPriority: authority cap not a TCB."
			       ">>"
			       "\n",
			       0lu, __func__, 1203, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	tcb_t *authTCB = ((tcb_t *)(cap_thread_cap_get_capTCBPtr(authCap)));
	exception_t status = checkPrio(newMcp, authTCB);
	if (status != EXCEPTION_NONE) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetMCPriority: Requested maximum controlled priority %lu too "
			       "high (max %lu)."
			       ">>"
			       "\n",
			       0lu, __func__, 1212, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), (unsigned long)newMcp,
			       (unsigned long)authTCB->tcbMCP);
		} while (0);
		return status;
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeTCB_ThreadControl(((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap))), NULL, 0,
				       newMcp, 0, cap_null_cap_new(), NULL, cap_null_cap_new(),
				       NULL, 0, cap_null_cap_new(), NULL,
				       thread_control_update_mcp);
}
exception_t decodeSetSchedParams(cap_t cap, word_t length, word_t *buffer)
{
	if (length < 2 || current_extra_caps.excaprefs[0] == NULL) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetSchedParams: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 1276, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	prio_t newMcp = getSyscallArg(0, buffer);
	prio_t newPrio = getSyscallArg(1, buffer);
	cap_t authCap = current_extra_caps.excaprefs[0]->cap;
	if (cap_get_capType(authCap) != cap_thread_cap) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetSchedParams: authority cap not a TCB."
			       ">>"
			       "\n",
			       0lu, __func__, 1291, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_InvalidCapability;
		current_syscall_error.invalidCapNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	tcb_t *authTCB = ((tcb_t *)(cap_thread_cap_get_capTCBPtr(authCap)));
	exception_t status = checkPrio(newMcp, authTCB);
	if (status != EXCEPTION_NONE) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetSchedParams: Requested maximum controlled priority %lu too "
			       "high (max %lu)."
			       ">>"
			       "\n",
			       0lu, __func__, 1300, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), (unsigned long)newMcp,
			       (unsigned long)authTCB->tcbMCP);
		} while (0);
		return status;
	}
	status = checkPrio(newPrio, authTCB);
	if (status != EXCEPTION_NONE) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetSchedParams: Requested priority %lu too high (max %lu)."
			       ">>"
			       "\n",
			       0lu, __func__, 1307, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), (unsigned long)newPrio,
			       (unsigned long)authTCB->tcbMCP);
		} while (0);
		return status;
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeTCB_ThreadControl(((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap))), NULL, 0,
				       newMcp, newPrio, cap_null_cap_new(), NULL,
				       cap_null_cap_new(), NULL, 0, cap_null_cap_new(), NULL,
				       thread_control_update_mcp | thread_control_update_priority);
}
exception_t decodeSetIPCBuffer(cap_t cap, word_t length, cte_t *slot, word_t *buffer)
{
	cptr_t cptr_bufferPtr;
	cap_t bufferCap;
	cte_t *bufferSlot;
	if (length < 1 || current_extra_caps.excaprefs[0] == NULL) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetIPCBuffer: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 1386, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	cptr_bufferPtr = getSyscallArg(0, buffer);
	bufferSlot = current_extra_caps.excaprefs[0];
	bufferCap = current_extra_caps.excaprefs[0]->cap;
	if (cptr_bufferPtr == 0) {
		bufferSlot = NULL;
	} else {
		exception_t e;
		deriveCap_ret_t dc_ret;
		dc_ret = deriveCap(bufferSlot, bufferCap);
		if (dc_ret.status != EXCEPTION_NONE) {
			return dc_ret.status;
		}
		bufferCap = dc_ret.cap;
		e = checkValidIPCBuffer(cptr_bufferPtr, bufferCap);
		if (e != EXCEPTION_NONE) {
			return e;
		}
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeTCB_ThreadControl(((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap))), slot, 0, 0,
				       0, cap_null_cap_new(), NULL, cap_null_cap_new(), NULL,
				       cptr_bufferPtr, bufferCap, bufferSlot,
				       thread_control_update_ipc_buffer);
}
exception_t decodeSetSpace(cap_t cap, word_t length, cte_t *slot, word_t *buffer)
{
	word_t cRootData, vRootData;
	cte_t *cRootSlot, *vRootSlot;
	cap_t cRootCap, vRootCap;
	deriveCap_ret_t dc_ret;
	if (length < 3 || current_extra_caps.excaprefs[0] == NULL ||
	    current_extra_caps.excaprefs[1] == NULL) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetSpace: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 1452, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	cptr_t faultEP = getSyscallArg(0, buffer);
	cRootData = getSyscallArg(1, buffer);
	vRootData = getSyscallArg(2, buffer);
	cRootSlot = current_extra_caps.excaprefs[0];
	cRootCap = current_extra_caps.excaprefs[0]->cap;
	vRootSlot = current_extra_caps.excaprefs[1];
	vRootCap = current_extra_caps.excaprefs[1]->cap;
	if (slotCapLongRunningDelete((((cte_t *)((word_t)(cap_thread_cap_get_capTCBPtr(cap)) &
						 ~((1ul << (11)) - 1ul))) +
				      (tcbCTable))) ||
	    slotCapLongRunningDelete((((cte_t *)((word_t)(cap_thread_cap_get_capTCBPtr(cap)) &
						 ~((1ul << (11)) - 1ul))) +
				      (tcbVTable)))) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetSpace: CSpace or VSpace currently being deleted."
			       ">>"
			       "\n",
			       0lu, __func__, 1482, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (cRootData != 0) {
		cRootCap = updateCapData(false, cRootData, cRootCap);
	}
	dc_ret = deriveCap(cRootSlot, cRootCap);
	if (dc_ret.status != EXCEPTION_NONE) {
		return dc_ret.status;
	}
	cRootCap = dc_ret.cap;
	if (cap_get_capType(cRootCap) != cap_cnode_cap) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetSpace: Invalid CNode cap."
			       ">>"
			       "\n",
			       0lu, __func__, 1498, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (vRootData != 0) {
		vRootCap = updateCapData(false, vRootData, vRootCap);
	}
	dc_ret = deriveCap(vRootSlot, vRootCap);
	if (dc_ret.status != EXCEPTION_NONE) {
		return dc_ret.status;
	}
	vRootCap = dc_ret.cap;
	if (!isValidVTableRoot(vRootCap)) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB SetSpace: Invalid VSpace cap."
			       ">>"
			       "\n",
			       0lu, __func__, 1514, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeTCB_ThreadControl(((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap))), slot,
				       faultEP, 0, 0, cRootCap, cRootSlot, vRootCap, vRootSlot, 0,
				       cap_null_cap_new(), NULL, thread_control_update_space);
}
exception_t decodeDomainInvocation(word_t invLabel, word_t length, word_t *buffer)
{
	word_t domain;
	cap_t tcap;
	if (__builtin_expect(!!(invLabel != DomainSetSet), 0)) {
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (__builtin_expect(!!(length == 0), 0)) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "Domain Configure: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 1559, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	} else {
		domain = getSyscallArg(0, buffer);
		if (domain >= numDomains) {
			do {
				printf("<<"
				       "seL4(CPU %"
				       "lu"
				       ")"
				       " [%s/%d T%p \"%s\" @%lx]: "
				       "Domain Configure: invalid domain (%lu >= %u)."
				       ">>"
				       "\n",
				       0lu, __func__, 1565, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread), domain, numDomains);
			} while (0);
			current_syscall_error.type = seL4_InvalidArgument;
			current_syscall_error.invalidArgumentNumber = 0;
			return EXCEPTION_SYSCALL_ERROR;
		}
	}
	if (__builtin_expect(!!(current_extra_caps.excaprefs[0] == NULL), 0)) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "Domain Configure: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 1574, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	tcap = current_extra_caps.excaprefs[0]->cap;
	if (__builtin_expect(!!(cap_get_capType(tcap) != cap_thread_cap), 0)) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "Domain Configure: thread cap required."
			       ">>"
			       "\n",
			       0lu, __func__, 1581, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_InvalidArgument;
		current_syscall_error.invalidArgumentNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	setDomain(((tcb_t *)(cap_thread_cap_get_capTCBPtr(tcap))), domain);
	return EXCEPTION_NONE;
}
exception_t decodeBindNotification(cap_t cap)
{
	notification_t *ntfnPtr;
	tcb_t *tcb;
	cap_t ntfn_cap;
	if (current_extra_caps.excaprefs[0] == NULL) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB BindNotification: Truncated message."
			       ">>"
			       "\n",
			       0lu, __func__, 1599, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	tcb = ((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap)));
	if (tcb->tcbBoundNotification) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB BindNotification: TCB already has a bound notification."
			       ">>"
			       "\n",
			       0lu, __func__, 1607, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	ntfn_cap = current_extra_caps.excaprefs[0]->cap;
	if (cap_get_capType(ntfn_cap) == cap_notification_cap) {
		ntfnPtr = ((notification_t *)(cap_notification_cap_get_capNtfnPtr(ntfn_cap)));
	} else {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB BindNotification: Notification is invalid."
			       ">>"
			       "\n",
			       0lu, __func__, 1617, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (!cap_notification_cap_get_capNtfnCanReceive(ntfn_cap)) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB BindNotification: Insufficient access rights"
			       ">>"
			       "\n",
			       0lu, __func__, 1623, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if ((tcb_t *)notification_ptr_get_ntfnQueue_head(ntfnPtr) ||
	    (tcb_t *)notification_ptr_get_ntfnBoundTCB(ntfnPtr)) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB BindNotification: Notification cannot be bound."
			       ">>"
			       "\n",
			       0lu, __func__, 1630, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeTCB_NotificationControl(tcb, ntfnPtr);
}
exception_t decodeUnbindNotification(cap_t cap)
{
	tcb_t *tcb;
	tcb = ((tcb_t *)(cap_thread_cap_get_capTCBPtr(cap)));
	if (!tcb->tcbBoundNotification) {
		do {
			printf("<<"
			       "seL4(CPU %"
			       "lu"
			       ")"
			       " [%s/%d T%p \"%s\" @%lx]: "
			       "TCB UnbindNotification: TCB already has no bound Notification."
			       ">>"
			       "\n",
			       0lu, __func__, 1647, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeTCB_NotificationControl(tcb, NULL);
}
/* The following functions sit in the preemption monad and implement the
 * preemptible, non-faulting bottom end of a TCB invocation. */
exception_t invokeTCB_Suspend(tcb_t *thread)
{
	suspend(thread);
	return EXCEPTION_NONE;
}
exception_t invokeTCB_Resume(tcb_t *thread)
{
	restart(thread);
	return EXCEPTION_NONE;
}
exception_t invokeTCB_ThreadControl(tcb_t *target, cte_t *slot, cptr_t faultep, prio_t mcp,
				    prio_t priority, cap_t cRoot_newCap, cte_t *cRoot_srcSlot,
				    cap_t vRoot_newCap, cte_t *vRoot_srcSlot, word_t bufferAddr,
				    cap_t bufferCap, cte_t *bufferSrcSlot,
				    thread_control_flag_t updateFlags)
{
	exception_t e;
	cap_t tCap = cap_thread_cap_new((word_t)target);
	if (updateFlags & thread_control_update_space) {
		target->tcbFaultHandler = faultep;
	}
	if (updateFlags & thread_control_update_mcp) {
		setMCPriority(target, mcp);
	}
	if (updateFlags & thread_control_update_space) {
		cte_t *rootSlot;
		rootSlot = (((cte_t *)((word_t)(target) & ~((1ul << (11)) - 1ul))) + (tcbCTable));
		e = cteDelete(rootSlot, true);
		if (e != EXCEPTION_NONE) {
			return e;
		}
		if (sameObjectAs(cRoot_newCap, cRoot_srcSlot->cap) &&
		    sameObjectAs(tCap, slot->cap)) {
			cteInsert(cRoot_newCap, cRoot_srcSlot, rootSlot);
		}
	}
	if (updateFlags & thread_control_update_space) {
		cte_t *rootSlot;
		rootSlot = (((cte_t *)((word_t)(target) & ~((1ul << (11)) - 1ul))) + (tcbVTable));
		e = cteDelete(rootSlot, true);
		if (e != EXCEPTION_NONE) {
			return e;
		}
		if (sameObjectAs(vRoot_newCap, vRoot_srcSlot->cap) &&
		    sameObjectAs(tCap, slot->cap)) {
			cteInsert(vRoot_newCap, vRoot_srcSlot, rootSlot);
		}
	}
	if (updateFlags & thread_control_update_ipc_buffer) {
		cte_t *bufferSlot;
		bufferSlot = (((cte_t *)((word_t)(target) & ~((1ul << (11)) - 1ul))) + (tcbBuffer));
		e = cteDelete(bufferSlot, true);
		if (e != EXCEPTION_NONE) {
			return e;
		}
		target->tcbIPCBuffer = bufferAddr;
		if (bufferSrcSlot && sameObjectAs(bufferCap, bufferSrcSlot->cap) &&
		    sameObjectAs(tCap, slot->cap)) {
			cteInsert(bufferCap, bufferSrcSlot, bufferSlot);
		}
		if (target == ksCurThread) {
			rescheduleRequired();
		}
	}
	if (updateFlags & thread_control_update_priority) {
		setPriority(target, priority);
	}
	return EXCEPTION_NONE;
}
exception_t invokeTCB_CopyRegisters(tcb_t *dest, tcb_t *tcb_src, bool_t suspendSource,
				    bool_t resumeTarget, bool_t transferFrame,
				    bool_t transferInteger, word_t transferArch)
{
	if (suspendSource) {
		suspend(tcb_src);
	}
	if (resumeTarget) {
		restart(dest);
	}
	if (transferFrame) {
		word_t i;
		word_t v;
		word_t pc;
		for (i = 0; i < n_frameRegisters; i++) {
			v = getRegister(tcb_src, frameRegisters[i]);
			setRegister(dest, frameRegisters[i], v);
		}
		pc = getRestartPC(dest);
		setNextPC(dest, pc);
	}
	if (transferInteger) {
		word_t i;
		word_t v;
		for (i = 0; i < n_gpRegisters; i++) {
			v = getRegister(tcb_src, gpRegisters[i]);
			setRegister(dest, gpRegisters[i], v);
		}
	}
	Arch_postModifyRegisters(dest);
	if (dest == ksCurThread) {
		/* If we modified the current thread we may need to reschedule
		 * due to changing registers are only reloaded in Arch_switchToThread */
		rescheduleRequired();
	}
	return Arch_performTransfer(transferArch, tcb_src, dest);
}
/* ReadRegisters is a special case: replyFromKernel & setMRs are
 * unfolded here, in order to avoid passing the large reply message up
 * to the top level in a global (and double-copying). We prevent the
 * top-level replyFromKernel_success_empty() from running by setting the
 * thread state. Retype does this too.
 */
exception_t invokeTCB_ReadRegisters(tcb_t *tcb_src, bool_t suspendSource, word_t n, word_t arch,
				    bool_t call)
{
	word_t i, j;
	exception_t e;
	tcb_t *thread;
	thread = ksCurThread;
	if (suspendSource) {
		suspend(tcb_src);
	}
	e = Arch_performTransfer(arch, tcb_src, ksCurThread);
	if (e != EXCEPTION_NONE) {
		return e;
	}
	if (call) {
		word_t *ipcBuffer;
		ipcBuffer = lookupIPCBuffer(true, thread);
		setRegister(thread, badgeRegister, 0);
		for (i = 0; i < n && i < n_frameRegisters && i < n_msgRegisters; i++) {
			setRegister(thread, msgRegisters[i],
				    getRegister(tcb_src, frameRegisters[i]));
		}
		if (ipcBuffer != NULL && i < n && i < n_frameRegisters) {
			for (; i < n && i < n_frameRegisters; i++) {
				ipcBuffer[i + 1] = getRegister(tcb_src, frameRegisters[i]);
			}
		}
		j = i;
		for (i = 0; i < n_gpRegisters && i + n_frameRegisters < n &&
			    i + n_frameRegisters < n_msgRegisters;
		     i++) {
			setRegister(thread, msgRegisters[i + n_frameRegisters],
				    getRegister(tcb_src, gpRegisters[i]));
		}
		if (ipcBuffer != NULL && i < n_gpRegisters && i + n_frameRegisters < n) {
			for (; i < n_gpRegisters && i + n_frameRegisters < n; i++) {
				ipcBuffer[i + n_frameRegisters + 1] =
					getRegister(tcb_src, gpRegisters[i]);
			}
		}
		setRegister(thread, msgInfoRegister,
			    wordFromMessageInfo(seL4_MessageInfo_new(0, 0, 0, i + j)));
	}
	setThreadState(thread, ThreadState_Running);
	return EXCEPTION_NONE;
}
exception_t invokeTCB_WriteRegisters(tcb_t *dest, bool_t resumeTarget, word_t n, word_t arch,
				     word_t *buffer)
{
	word_t i;
	word_t pc;
	exception_t e;
	bool_t archInfo;
	e = Arch_performTransfer(arch, ksCurThread, dest);
	if (e != EXCEPTION_NONE) {
		return e;
	}
	if (n > n_frameRegisters + n_gpRegisters) {
		n = n_frameRegisters + n_gpRegisters;
	}
	archInfo = Arch_getSanitiseRegisterInfo(dest);
	for (i = 0; i < n_frameRegisters && i < n; i++) {
		/* Offset of 2 to get past the initial syscall arguments */
		setRegister(dest, frameRegisters[i],
			    sanitiseRegister(frameRegisters[i], getSyscallArg(i + 2, buffer),
					     archInfo));
	}
	for (i = 0; i < n_gpRegisters && i + n_frameRegisters < n; i++) {
		setRegister(dest, gpRegisters[i],
			    sanitiseRegister(gpRegisters[i],
					     getSyscallArg(i + n_frameRegisters + 2, buffer),
					     archInfo));
	}
	pc = getRestartPC(dest);
	setNextPC(dest, pc);
	Arch_postModifyRegisters(dest);
	if (resumeTarget) {
		restart(dest);
	}
	if (dest == ksCurThread) {
		/* If we modified the current thread we may need to reschedule
		 * due to changing registers are only reloaded in Arch_switchToThread */
		rescheduleRequired();
	}
	return EXCEPTION_NONE;
}
exception_t invokeTCB_NotificationControl(tcb_t *tcb, notification_t *ntfnPtr)
{
	if (ntfnPtr) {
		bindNotification(tcb, ntfnPtr);
	} else {
		unbindNotification(tcb);
	}
	return EXCEPTION_NONE;
}
void setThreadName(tcb_t *tcb, const char *name)
{
	strlcpy(((debug_tcb_t *)(((cte_t *)((word_t)(tcb) & ~((1ul << (11)) - 1ul))) +
				 (tcbCNodeEntries)))
			->tcbName,
		name,
		((1ul << (11 - 1)) - (tcbCNodeEntries * sizeof(cte_t)) - sizeof(debug_tcb_t)));
}
word_t setMRs_syscall_error(tcb_t *thread, word_t *receiveIPCBuffer)
{
	switch (current_syscall_error.type) {
	case seL4_InvalidArgument:
		return setMR(thread, receiveIPCBuffer, 0,
			     current_syscall_error.invalidArgumentNumber);
	case seL4_InvalidCapability:
		return setMR(thread, receiveIPCBuffer, 0, current_syscall_error.invalidCapNumber);
	case seL4_IllegalOperation:
		return 0;
	case seL4_RangeError:
		setMR(thread, receiveIPCBuffer, 0, current_syscall_error.rangeErrorMin);
		return setMR(thread, receiveIPCBuffer, 1, current_syscall_error.rangeErrorMax);
	case seL4_AlignmentError:
		return 0;
	case seL4_FailedLookup:
		setMR(thread, receiveIPCBuffer, 0,
		      current_syscall_error.failedLookupWasSource ? 1 : 0);
		return setMRs_lookup_failure(thread, receiveIPCBuffer, current_lookup_fault, 1);
	case seL4_TruncatedMessage:
	case seL4_DeleteFirst:
	case seL4_RevokeFirst:
		return 0;
	case seL4_NotEnoughMemory:
		return setMR(thread, receiveIPCBuffer, 0, current_syscall_error.memoryLeft);
	default:
		_fail("Invalid syscall error",
		      "/home/lab/projects/seL4/seL4test/kernel/src/object/tcb.c", 2082, __func__);
	}
}
static word_t alignUp(word_t baseValue, word_t alignment)
{
	return (baseValue + (BIT(alignment) - 1)) & ~MASK(alignment);
}
exception_t decodeUntypedInvocation(word_t invLabel, word_t length, cte_t *slot, cap_t cap,
				    bool_t call, word_t *buffer)
{
	word_t newType, userObjSize, nodeIndex;
	word_t nodeDepth, nodeOffset, nodeWindow;
	cte_t *rootSlot;
	exception_t status;
	cap_t nodeCap;
	lookupSlot_ret_t lu_ret;
	word_t nodeSize;
	word_t i;
	cte_t *destCNode;
	word_t freeRef, alignedFreeRef, objectSize, untypedFreeBytes;
	word_t freeIndex;
	bool_t deviceMemory;
	bool_t reset;
	/* Ensure operation is valid. */
	if (invLabel != UntypedRetype) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped cap: Illegal "
			       "operation attempted.>>\n",
			       0lu, __func__, 45, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_IllegalOperation;
		return EXCEPTION_SYSCALL_ERROR;
	}
	/* Ensure message length valid. */
	if (length < 6 || current_extra_caps.excaprefs[0] == NULL) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped invocation: "
			       "Truncated message.>>\n",
			       0lu, __func__, 52, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_TruncatedMessage;
		return EXCEPTION_SYSCALL_ERROR;
	}
	/* Fetch arguments. */
	newType = getSyscallArg(0, buffer);
	userObjSize = getSyscallArg(1, buffer);
	nodeIndex = getSyscallArg(2, buffer);
	nodeDepth = getSyscallArg(3, buffer);
	nodeOffset = getSyscallArg(4, buffer);
	nodeWindow = getSyscallArg(5, buffer);
	rootSlot = current_extra_caps.excaprefs[0];
	/* Is the requested object type valid? */
	if (newType >= seL4_ObjectTypeCount) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: Invalid "
			       "object type.>>\n",
			       0lu, __func__, 69, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_InvalidArgument;
		current_syscall_error.invalidArgumentNumber = 0;
		return EXCEPTION_SYSCALL_ERROR;
	}
	objectSize = getObjectSize(newType, userObjSize);
	/* Exclude impossibly large object sizes. getObjectSize can overflow if userObjSize
	   is close to 2^wordBits, which is nonsensical in any case, so we check that this
	   did not happen. userObjSize will always need to be less than wordBits. */
	if (userObjSize >= (1 << 6) || objectSize > 47) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: Invalid "
			       "object size.>>\n",
			       0lu, __func__, 81, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_RangeError;
		current_syscall_error.rangeErrorMin = 0;
		current_syscall_error.rangeErrorMax = 47;
		return EXCEPTION_SYSCALL_ERROR;
	}
	/* If the target object is a CNode, is it at least size 1? */
	if (newType == seL4_CapTableObject && userObjSize == 0) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: Requested "
			       "CapTable size too small.>>\n",
			       0lu, __func__, 90, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_InvalidArgument;
		current_syscall_error.invalidArgumentNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	/* If the target object is a Untyped, is it at least size 4? */
	if (newType == seL4_UntypedObject && userObjSize < 4) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: Requested "
			       "UntypedItem size too small.>>\n",
			       0lu, __func__, 98, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_InvalidArgument;
		current_syscall_error.invalidArgumentNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	/* Lookup the destination CNode (where our caps will be placed in). */
	if (nodeDepth == 0) {
		nodeCap = current_extra_caps.excaprefs[0]->cap;
	} else {
		cap_t rootCap = current_extra_caps.excaprefs[0]->cap;
		lu_ret = lookupTargetSlot(rootCap, nodeIndex, nodeDepth);
		if (lu_ret.status != EXCEPTION_NONE) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: "
				       "Invalid destination address.>>\n",
				       0lu, __func__, 120, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread));
			} while (0);
			return lu_ret.status;
		}
		nodeCap = lu_ret.slot->cap;
	}
	/* Is the destination actually a CNode? */
	if (cap_get_capType(nodeCap) != cap_cnode_cap) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: "
			       "Destination cap invalid or read-only.>>\n",
			       0lu, __func__, 128, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_FailedLookup;
		current_syscall_error.failedLookupWasSource = 0;
		current_lookup_fault = lookup_fault_missing_capability_new(nodeDepth);
		return EXCEPTION_SYSCALL_ERROR;
	}
	/* Is the region where the user wants to put the caps valid? */
	nodeSize = 1ul << cap_cnode_cap_get_capCNodeRadix(nodeCap);
	if (nodeOffset > nodeSize - 1) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: "
			       "Destination node offset #%d too large.>>\n",
			       0lu, __func__, 138, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), (int)nodeOffset);
		} while (0);
		current_syscall_error.type = seL4_RangeError;
		current_syscall_error.rangeErrorMin = 0;
		current_syscall_error.rangeErrorMax = nodeSize - 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (nodeWindow < 1 || nodeWindow > 256) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: Number of "
			       "requested objects (%d) too small or large.>>\n",
			       0lu, __func__, 146, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), (int)nodeWindow);
		} while (0);
		current_syscall_error.type = seL4_RangeError;
		current_syscall_error.rangeErrorMin = 1;
		current_syscall_error.rangeErrorMax = 256;
		return EXCEPTION_SYSCALL_ERROR;
	}
	if (nodeWindow > nodeSize - nodeOffset) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: Requested "
			       "destination window overruns size of node.>>\n",
			       0lu, __func__, 154, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_RangeError;
		current_syscall_error.rangeErrorMin = 1;
		current_syscall_error.rangeErrorMax = nodeSize - nodeOffset;
		return EXCEPTION_SYSCALL_ERROR;
	}
	/* Ensure that the destination slots are all empty. */
	destCNode = ((cte_t *)(cap_cnode_cap_get_capCNodePtr(nodeCap)));
	for (i = nodeOffset; i < nodeOffset + nodeWindow; i++) {
		status = ensureEmptySlot(destCNode + i);
		if (status != EXCEPTION_NONE) {
			do {
				printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: "
				       "Slot #%d in destination window non-empty.>>\n",
				       0lu, __func__, 166, ksCurThread,
				       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
								   ~((1ul << (11)) - 1ul))) +
							(tcbCNodeEntries)))
					       ->tcbName,
				       (word_t)getRestartPC(ksCurThread), (int)i);
			} while (0);
			return status;
		}
	}
	/*
	 * Determine where in the Untyped region we should start allocating new
	 * objects.
	 *
	 * If we have no children, we can start allocating from the beginning of
	 * our untyped, regardless of what the "free" value in the cap states.
	 * (This may happen if all of the objects beneath us got deleted).
	 *
	 * If we have children, we just keep allocating from the "free" value
	 * recorded in the cap.
	 */
	status = ensureNoChildren(slot);
	if (status != EXCEPTION_NONE) {
		freeIndex = cap_untyped_cap_get_capFreeIndex(cap);
		reset = false;
	} else {
		freeIndex = 0;
		reset = true;
	}
	freeRef = ((word_t)(((word_t)(cap_untyped_cap_get_capPtr(cap))) + ((freeIndex) << 4)));
	/*
	 * Determine the maximum number of objects we can create, and return an
	 * error if we don't have enough space.
	 *
	 * We don't need to worry about alignment in this case, because if anything
	 * fits, it will also fit aligned up (by packing it on the right hand side
	 * of the untyped).
	 */
	untypedFreeBytes = (1ul << (cap_untyped_cap_get_capBlockSize(cap))) - ((freeIndex) << 4);
	if ((untypedFreeBytes >> objectSize) < nodeWindow) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: "
			       "Insufficient memory (%lu * %lu bytes needed, %lu bytes "
			       "available).>>\n",
			       0lu, __func__, 205, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread), (word_t)nodeWindow,
			       (objectSize >= (1 << 6) ? -1 : (1ul << objectSize)),
			       (word_t)(untypedFreeBytes));
		} while (0);
		current_syscall_error.type = seL4_NotEnoughMemory;
		current_syscall_error.memoryLeft = untypedFreeBytes;
		return EXCEPTION_SYSCALL_ERROR;
	}
	deviceMemory = cap_untyped_cap_get_capIsDevice(cap);
	if ((deviceMemory && !Arch_isFrameType(newType)) && newType != seL4_UntypedObject) {
		do {
			printf("<<seL4(CPU %lu) [%s/%d T%p \"%s\" @%lx]: Untyped Retype: Creating "
			       "kernel objects with device untyped>>\n",
			       0lu, __func__, 218, ksCurThread,
			       ((debug_tcb_t *)(((cte_t *)((word_t)(ksCurThread) &
							   ~((1ul << (11)) - 1ul))) +
						(tcbCNodeEntries)))
				       ->tcbName,
			       (word_t)getRestartPC(ksCurThread));
		} while (0);
		current_syscall_error.type = seL4_InvalidArgument;
		current_syscall_error.invalidArgumentNumber = 1;
		return EXCEPTION_SYSCALL_ERROR;
	}
	/* Align up the free region so that it is aligned to the target object's
	 * size. */
	alignedFreeRef = alignUp(freeRef, objectSize);
	/* Perform the retype. */
	setThreadState(ksCurThread, ThreadState_Restart);
	return invokeUntyped_Retype(slot, reset, (void *)alignedFreeRef, newType, userObjSize,
				    destCNode, nodeOffset, nodeWindow, deviceMemory);
}
static exception_t resetUntypedCap(cte_t *srcSlot)
{
	cap_t prev_cap = srcSlot->cap;
	word_t block_size = cap_untyped_cap_get_capBlockSize(prev_cap);
	void *regionBase = ((word_t *)(cap_untyped_cap_get_capPtr(prev_cap)));
	int chunk = 8;
	word_t offset = ((cap_untyped_cap_get_capFreeIndex(prev_cap)) << 4);
	exception_t status;
	bool_t deviceMemory = cap_untyped_cap_get_capIsDevice(prev_cap);
	if (offset == 0) {
		return EXCEPTION_NONE;
	}
	/** AUXUPD: "(True, typ_region_bytes (ptr_val \<acute>regionBase)
	    (unat \<acute>block_size))" */
	/** GHOSTUPD: "(True, gs_clear_region (ptr_val \<acute>regionBase)
	    (unat \<acute>block_size))" */
	if (deviceMemory || block_size < chunk) {
		if (!deviceMemory) {
			clearMemory(regionBase, block_size);
		}
		srcSlot->cap = cap_untyped_cap_set_capFreeIndex(prev_cap, 0);
	} else {
		for (offset = (((offset - 1) >> (chunk)) << (chunk)); offset != -(1ul << (chunk));
		     offset -= (1ul << (chunk))) {
			clearMemory(((void *)(((word_t)(regionBase)) + (offset))), chunk);
			srcSlot->cap = cap_untyped_cap_set_capFreeIndex(prev_cap, ((offset) >> 4));
			status = preemptionPoint();
			if (status != EXCEPTION_NONE) {
				return status;
			}
		}
	}
	return EXCEPTION_NONE;
}
exception_t invokeUntyped_Retype(cte_t *srcSlot, bool_t reset, void *retypeBase, object_t newType,
				 word_t userSize, cte_t *destCNode, word_t destOffset,
				 word_t destLength, bool_t deviceMemory)
{
	word_t freeRef;
	word_t totalObjectSize;
	void *regionBase = ((word_t *)(cap_untyped_cap_get_capPtr(srcSlot->cap)));
	exception_t status;
	if (reset) {
		status = resetUntypedCap(srcSlot);
		if (status != EXCEPTION_NONE) {
			return status;
		}
	}
	/* Update the amount of free space left in this untyped cap.
	 *
	 * Note that userSize is not necessarily the true size of the object in
	 * memory. In the case where newType is seL4_CapTableObject, the size is
	 * transformed by getObjectSize. */
	totalObjectSize = destLength << getObjectSize(newType, userSize);
	freeRef = (word_t)retypeBase + totalObjectSize;
	srcSlot->cap = cap_untyped_cap_set_capFreeIndex(
		srcSlot->cap, (((word_t)(freeRef) - (word_t)(regionBase)) >> 4));
	/* Create new objects and caps. */
	createNewObjects(newType, srcSlot, destCNode, destOffset, destLength, retypeBase, userSize,
			 deviceMemory);
	return EXCEPTION_NONE;
}
word_t strnlen(const char *s, word_t maxlen)
{
	word_t len;
	for (len = 0; len < maxlen && s[len]; len++)
		;
	return len;
}
word_t strlcpy(char *dest, const char *src, word_t size)
{
	word_t len;
	for (len = 0; len + 1 < size && src[len]; len++) {
		dest[len] = src[len];
	}
	dest[len] = '\0';
	return len;
}
word_t strlcat(char *dest, const char *src, word_t size)
{
	word_t len;
	/* get to the end of dest */
	for (len = 0; len < size && dest[len]; len++)
		;
	/* check that dest was at least 'size' length to prevent inserting
	 * a null byte when we shouldn't */
	if (len < size) {
		for (; len + 1 < size && *src; len++, src++) {
			dest[len] = *src;
		}
		dest[len] = '\0';
	}
	return len;
}
/*
 * memzero needs a custom type that allows us to use a word
 * that has the aliasing properties of a char.
 */
typedef unsigned long __attribute__((__may_alias__)) ulong_alias;
/*
 * Zero 'n' bytes of memory starting from 's'.
 *
 * 'n' and 's' must be word aligned.
 */
void memzero(void *s, unsigned long n)
{
	uint8_t *p = s;
	/* Ensure alignment constraints are met. */
	/* We will never memzero an area larger than the largest current
	   live object */
	/** GHOSTUPD: "(gs_get_assn cap_get_capSizeBits_'proc \<acute>ghost'state = 0
	    \<or> \<acute>n <= gs_get_assn cap_get_capSizeBits_'proc \<acute>ghost'state, id)" */
	/* Write out words. */
	while (n != 0) {
		*(ulong_alias *)p = 0;
		p += sizeof(ulong_alias);
		n -= sizeof(ulong_alias);
	}
}
void *memset(void *s, unsigned long c, unsigned long n)
{
	uint8_t *p;
	/*
	 * If we are only writing zeros and we are word aligned, we can
	 * use the optimized 'memzero' function.
	 */
	if (__builtin_expect(!!(c == 0 && ((unsigned long)s % sizeof(unsigned long)) == 0 &&
				(n % sizeof(unsigned long)) == 0),
			     1)) {
		memzero(s, n);
	} else {
		/* Otherwise, we use a slower, simple memset. */
		for (p = (uint8_t *)s; n > 0; n--, p++) {
			*p = (uint8_t)c;
		}
	}
	return s;
}
void *memcpy(void *ptr_dst, const void *ptr_src, unsigned long n)
{
	uint8_t *p;
	const uint8_t *q;
	for (p = (uint8_t *)ptr_dst, q = (const uint8_t *)ptr_src; n; n--, p++, q++) {
		*p = *q;
	}
	return ptr_dst;
}
int strncmp(const char *s1, const char *s2, int n)
{
	word_t i;
	int diff;
	for (i = 0; i < n; i++) {
		diff = ((unsigned char *)s1)[i] - ((unsigned char *)s2)[i];
		if (diff != 0 || s1[i] == '\0') {
			return diff;
		}
	}
	return 0;
}
long char_to_long(char c)
{
	if (c >= '0' && c <= '9') {
		return c - '0';
	} else if (c >= 'A' && c <= 'F') {
		return c - 'A' + 10;
	} else if (c >= 'a' && c <= 'f') {
		return c - 'a' + 10;
	}
	return -1;
}
long str_to_long(const char *str)
{
	unsigned int base;
	long res;
	long val = 0;
	char c;
	/*check for "0x" */
	if (*str == '0' && (*(str + 1) == 'x' || *(str + 1) == 'X')) {
		base = 16;
		str += 2;
	} else {
		base = 10;
	}
	if (!*str) {
		return -1;
	}
	c = *str;
	while (c != '\0') {
		res = char_to_long(c);
		if (res == -1 || res >= base) {
			return -1;
		}
		val = val * base + res;
		str++;
		c = *str;
	}
	return val;
}
// The following implementations of CLZ (count leading zeros) and CTZ (count
// trailing zeros) perform a binary search for the first 1 bit from the
// beginning (resp. end) of the input. Initially, the focus is the whole input.
// Then, each iteration determines whether there are any 1 bits set in the
// upper (resp. lower) half of the current focus. If there are (resp. are not),
// then the upper half is shifted into the lower half. Either way, the lower
// half of the current focus becomes the new focus for the next iteration.
// After enough iterations (6 for 64-bit inputs, 5 for 32-bit inputs), the
// focus is reduced to a single bit, and the total number of bits shifted can
// be used to determine the number of zeros before (resp. after) the first 1
// bit.
//
// Although the details vary, the general approach is used in several library
// implementations, including in LLVM and GCC. Wikipedia has some references:
// https://en.wikipedia.org/wiki/Find_first_set
//
// The current implementation avoids branching. The test that determines
// whether the upper (resp. lower) half contains any ones directly produces a
// number which can be used for an unconditional shift. If the upper (resp.
// lower) half is all zeros, the test produces a zero, and the shift is a
// no-op. A branchless implementation has the disadvantage that it requires
// more instructions to execute than one which branches, but the advantage is
// that none will be mispredicted branches. Whether this is a good tradeoff
// depends on the branch predictability and the architecture's pipeline depth.
// The most critical use of clzl in the kernel is in the scheduler priority
// queue. In the absence of a concrete application and hardware implementation
// to evaluate the tradeoff, we somewhat arbitrarily choose a branchless
// implementation. In any case, the compiler might convert this to a branching
// binary.
// Check some assumptions made by the clzl, clzll, ctzl functions:
_Static_assert(sizeof(unsigned long) == 4 || sizeof(unsigned long) == 8, "clz_ulong_32_or_64");
;
_Static_assert(sizeof(unsigned long long) == 8, "clz_ullong_64");
;
_Static_assert(sizeof(unsigned long) * 8 == 64, "clz_word_size");
;
// Count leading zeros.
// This implementation contains no branches. If the architecture provides an
// instruction to set a register to a boolean value on a comparison, then the
// binary might also avoid branching. A branchless implementation might be
// preferable on architectures with deep pipelines, or when the maximum
// priority of runnable threads frequently varies. However, note that the
// compiler may choose to convert this to a branching implementation.
//
// These functions are potentially `UNUSED` because we want to always expose
// them to verification without necessarily linking them into the kernel
// binary.
static inline unsigned clz32(uint32_t x)
{
	// Compiler builtins typically return int, but we use unsigned internally
	// to reduce the number of guards we see in the proofs.
	unsigned count = 32;
	uint32_t mask = (0xFFFFFFFF);
	// Each iteration i (counting backwards) considers the least significant
	// 2^(i+1) bits of x as the current focus. At the first iteration, the
	// focus is the whole input. Each iteration assumes x contains no 1 bits
	// outside its focus. The iteration contains a test which determines
	// whether there are any 1 bits in the upper half (2^i bits) of the focus,
	// setting `bits` to 2^i if there are, or zero if not. Shifting by `bits`
	// then narrows the focus to the lower 2^i bits and satisfies the
	// assumption for the next iteration. After the final iteration, the focus
	// is just the least significant bit, and the most significsnt 1 bit of the
	// original input (if any) has been shifted into this position. The leading
	// zero count can be determined from the total shift.
	//
	// The iterations are given a very regular structure to facilitate proofs,
	// while also generating reasonably efficient binary code.
	// The `if (1)` blocks make it easier to reason by chunks in the proofs.
	if (1) {
		// iteration 4
		mask >>= (1 << 4);			     // 0x0000ffff
		unsigned bits = ((unsigned)(mask < x)) << 4; // [0, 16]
		x >>= bits;				     // <= 0x0000ffff
		count -= bits;				     // [16, 32]
	}
	if (1) {
		// iteration 3
		mask >>= (1 << 3);			     // 0x000000ff
		unsigned bits = ((unsigned)(mask < x)) << 3; // [0, 8]
		x >>= bits;				     // <= 0x000000ff
		count -= bits;				     // [8, 16, 24, 32]
	}
	if (1) {
		// iteration 2
		mask >>= (1 << 2);			     // 0x0000000f
		unsigned bits = ((unsigned)(mask < x)) << 2; // [0, 4]
		x >>= bits;				     // <= 0x0000000f
		count -= bits;				     // [4, 8, 12, ..., 32]
	}
	if (1) {
		// iteration 1
		mask >>= (1 << 1);			     // 0x00000003
		unsigned bits = ((unsigned)(mask < x)) << 1; // [0, 2]
		x >>= bits;				     // <= 0x00000003
		count -= bits;				     // [2, 4, 6, ..., 32]
	}
	if (1) {
		// iteration 0
		mask >>= (1 << 0);			     // 0x00000001
		unsigned bits = ((unsigned)(mask < x)) << 0; // [0, 1]
		x >>= bits;				     // <= 0x00000001
		count -= bits;				     // [1, 2, 3, ..., 32]
	}
	// If the original input was zero, there will have been no shifts, so this
	// gives a result of 32. Otherwise, x is now exactly 1, so subtracting from
	// count gives a result from [0, 1, 2, ..., 31].
	return count - x;
}
static inline unsigned clz64(uint64_t x)
{
	unsigned count = 64;
	uint64_t mask = (0xFFFFFFFFFFFFFFFF);
	// Although we could implement this using clz32, we spell out the
	// iterations in full for slightly better code generation at low
	// optimisation levels, and to allow us to reuse the proof machinery we
	// developed for clz32.
	if (1) {
		// iteration 5
		mask >>= (1 << 5);			     // 0x00000000ffffffff
		unsigned bits = ((unsigned)(mask < x)) << 5; // [0, 32]
		x >>= bits;				     // <= 0x00000000ffffffff
		count -= bits;				     // [32, 64]
	}
	if (1) {
		// iteration 4
		mask >>= (1 << 4);			     // 0x000000000000ffff
		unsigned bits = ((unsigned)(mask < x)) << 4; // [0, 16]
		x >>= bits;				     // <= 0x000000000000ffff
		count -= bits;				     // [16, 32, 48, 64]
	}
	if (1) {
		// iteration 3
		mask >>= (1 << 3);			     // 0x00000000000000ff
		unsigned bits = ((unsigned)(mask < x)) << 3; // [0, 8]
		x >>= bits;				     // <= 0x00000000000000ff
		count -= bits;				     // [8, 16, 24, ..., 64]
	}
	if (1) {
		// iteration 2
		mask >>= (1 << 2);			     // 0x000000000000000f
		unsigned bits = ((unsigned)(mask < x)) << 2; // [0, 4]
		x >>= bits;				     // <= 0x000000000000000f
		count -= bits;				     // [4, 8, 12, ..., 64]
	}
	if (1) {
		// iteration 1
		mask >>= (1 << 1);			     // 0x0000000000000003
		unsigned bits = ((unsigned)(mask < x)) << 1; // [0, 2]
		x >>= bits;				     // <= 0x0000000000000003
		count -= bits;				     // [2, 4, 6, ..., 64]
	}
	if (1) {
		// iteration 0
		mask >>= (1 << 0);			     // 0x0000000000000001
		unsigned bits = ((unsigned)(mask < x)) << 0; // [0, 1]
		x >>= bits;				     // <= 0x0000000000000001
		count -= bits;				     // [1, 2, 3, ..., 64]
	}
	return count - x;
}
// Count trailing zeros.
// See comments on clz32.
static inline unsigned ctz32(uint32_t x)
{
	unsigned count = (x == 0);
	uint32_t mask = (0xFFFFFFFF);
	// Each iteration i (counting backwards) considers the least significant
	// 2^(i+1) bits of x as the current focus. At the first iteration, the
	// focus is the whole input. The iteration contains a test which determines
	// whether there are any 1 bits in the lower half (2^i bits) of the focus,
	// setting `bits` to zero if there are, or 2^i if not. Shifting by `bits`
	// then narrows the focus to the lower 2^i bits for the next iteration.
	// After the final iteration, the focus is just the least significant bit,
	// and the least significsnt 1 bit of the original input (if any) has been
	// shifted into this position. The trailing zero count can be determined
	// from the total shift.
	//
	// If the initial input is zero, every iteration causes a shift, for a
	// total shift count of 31, so in that case, we add one for a total count
	// of 32. In the comments, xi is the initial value of x.
	//
	// The iterations are given a very regular structure to facilitate proofs,
	// while also generating reasonably efficient binary code.
	if (1) {
		// iteration 4
		mask >>= (1 << 4);				    // 0x0000ffff
		unsigned bits = ((unsigned)((x & mask) == 0)) << 4; // [0, 16]
		x >>= bits;    // xi != 0 --> x & 0x0000ffff != 0
		count += bits; // if xi != 0 then [0, 16] else 17
	}
	if (1) {
		// iteration 3
		mask >>= (1 << 3);				    // 0x000000ff
		unsigned bits = ((unsigned)((x & mask) == 0)) << 3; // [0, 8]
		x >>= bits;    // xi != 0 --> x & 0x000000ff != 0
		count += bits; // if xi != 0 then [0, 8, 16, 24] else 25
	}
	if (1) {
		// iteration 2
		mask >>= (1 << 2);				    // 0x0000000f
		unsigned bits = ((unsigned)((x & mask) == 0)) << 2; // [0, 4]
		x >>= bits;    // xi != 0 --> x & 0x0000000f != 0
		count += bits; // if xi != 0 then [0, 4, 8, ..., 28] else 29
	}
	if (1) {
		// iteration 1
		mask >>= (1 << 1);				    // 0x00000003
		unsigned bits = ((unsigned)((x & mask) == 0)) << 1; // [0, 2]
		x >>= bits;    // xi != 0 --> x & 0x00000003 != 0
		count += bits; // if xi != 0 then [0, 2, 4, ..., 30] else 31
	}
	if (1) {
		// iteration 0
		mask >>= (1 << 0);				    // 0x00000001
		unsigned bits = ((unsigned)((x & mask) == 0)) << 0; // [0, 1]
		x >>= bits;    // xi != 0 --> x & 0x00000001 != 0
		count += bits; // if xi != 0 then [0, 1, 2, ..., 31] else 32
	}
	return count;
}
static inline unsigned ctz64(uint64_t x)
{
	unsigned count = (x == 0);
	uint64_t mask = (0xFFFFFFFFFFFFFFFF);
	if (1) {
		// iteration 5
		mask >>= (1 << 5);				    // 0x00000000ffffffff
		unsigned bits = ((unsigned)((x & mask) == 0)) << 5; // [0, 32]
		x >>= bits;    // xi != 0 --> x & 0x00000000ffffffff != 0
		count += bits; // if xi != 0 then [0, 32] else 33
	}
	if (1) {
		// iteration 4
		mask >>= (1 << 4);				    // 0x000000000000ffff
		unsigned bits = ((unsigned)((x & mask) == 0)) << 4; // [0, 16]
		x >>= bits;    // xi != 0 --> x & 0x000000000000ffff != 0
		count += bits; // if xi != 0 then [0, 16, 32, 48] else 49
	}
	if (1) {
		// iteration 3
		mask >>= (1 << 3);				    // 0x00000000000000ff
		unsigned bits = ((unsigned)((x & mask) == 0)) << 3; // [0, 8]
		x >>= bits;    // xi != 0 --> x & 0x00000000000000ff != 0
		count += bits; // if xi != 0 then [0, 8, 16, ..., 56] else 57
	}
	if (1) {
		// iteration 2
		mask >>= (1 << 2);				    // 0x000000000000000f
		unsigned bits = ((unsigned)((x & mask) == 0)) << 2; // [0, 4]
		x >>= bits;    // xi != 0 --> x & 0x000000000000000f != 0
		count += bits; // if xi != 0 then [0, 4, 8, ..., 60] else 61
	}
	if (1) {
		// iteration 1
		mask >>= (1 << 1);				    // 0x0000000000000003
		unsigned bits = ((unsigned)((x & mask) == 0)) << 1; // [0, 2]
		x >>= bits;    // xi != 0 --> x & 0x0000000000000003 != 0
		count += bits; // if xi != 0 then [0, 2, 4, ..., 62] else 63
	}
	if (1) {
		// iteration 0
		mask >>= (1 << 0);				    // 0x0000000000000001
		unsigned bits = ((unsigned)((x & mask) == 0)) << 0; // [0, 1]
		x >>= bits;    // xi != 0 --> x & 0x0000000000000001 != 0
		count += bits; // if xi != 0 then [0, 1, 2, ..., 63] else 64
	}
	return count;
}
// GCC's builtins will emit calls to these functions when the platform does
// not provide suitable inline assembly.
// These are only provided when the relevant config items are set.
// We define these separately from `ctz32` etc. so that we can verify all of
// `ctz32` etc. without necessarily linking them into the kernel binary.
/* This is a domain schedule that is suitable for the domains tests in sel4test. All
 * sel4test actually needs is for every domain to be executable for some period of time
 * in order for the tests to make progress
 */
/* remember that this is compiled as part of the kernel, and so is referencing kernel headers */
/* Default schedule. */
const dschedule_t ksDomSchedule[] = {
	{.domain = 0, .length = 1},
};
const word_t ksDomScheduleLength = sizeof(ksDomSchedule) / sizeof(dschedule_t);
