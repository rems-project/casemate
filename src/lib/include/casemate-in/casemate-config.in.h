#ifndef CASEMATE_CONFIG_H
#define CASEMATE_CONFIG_H

//////////////
// Configuration

typedef enum {
	CM_PRINT_NONE = 0,

	CM_PRINT_WHOLE_STATE_ON_STEP = 1,
	CM_PRINT_DIFF_TO_STATE_ON_STEP = 2,
	CM_PRINT_ONLY_UNCLEAN = 4,

	CM_PRINT_ALL = CM_PRINT_WHOLE_STATE_ON_STEP | CM_PRINT_DIFF_TO_STATE_ON_STEP,
	CM_PRINT_ALL_CONDENSED = CM_PRINT_ALL | CM_PRINT_ONLY_UNCLEAN,
} casemate_print_opts_t;

#define CASEMATE_DEFAULT_PRINT_OPTS \
	CM_PRINT_NONE

struct casemate_checker_options {
	/**
	 * @promote_DSB_nsh: Silently promote all DSB NSH to DSB ISH
	 */
	bool promote_DSB_nsh;

	/**
	 * @promote_TLBI_nsh: Silently promote all TLBI to broadcast ones
	 */
	bool promote_TLBI_nsh;

	/**
	 * @promote_TLBI_by_id: Silently promote all TLBI-by-ASID and by-VMID to ALL
	 */
	bool promote_TLBI_by_id;

	/**
	 * @enable_printing: print out the current state of the
	 * @print_opts: logging to perform.
	 */
	bool enable_printing;
	casemate_print_opts_t print_opts;
};

#define CASEMATE_DEFAULT_CHECK_OPTS \
	(struct casemate_checker_options){ \
		.promote_DSB_nsh = false, \
		.promote_TLBI_nsh = false, \
		.promote_TLBI_by_id = false, \
		.enable_printing = false, \
		.print_opts = CASEMATE_DEFAULT_PRINT_OPTS, \
	}

struct casemate_log_options {
	/**
	 * @log_format_version: Version of the log format
	 */
	unsigned int log_format_version;

	/**
	 * @condensed_format: if true, trace omits the keys in key/value pairs.
	 */
	bool condensed_format;
};

#define CASEMATE_DEFAULT_LOG_OPTS \
	(struct casemate_log_options){ \
		.log_format_version = 1, \
		.condensed_format = false, \
	}

/**
 * struct casemate_options - Global configuration of ghost model behaviour
 *
 * Provides selective enabling/disabling of supported behaviours.
 */
struct casemate_options {
	/**
	 * @enable_tracing: Printing tracepoints
	 */
	bool enable_tracing;

	/**
	 * @enable_checking: Turn on/off runtime model checking
	 */
	bool enable_checking;

	/**
	 * @log_opts: Options for logging
	 */
	struct casemate_log_options log_opts;

	/**
	 * @check_opts: Options for checker
	 */
	struct casemate_checker_options check_opts;

	/**
	 * @enable_safety_checks: Enables non-functional model-internal consistency checks.
	 */
	bool enable_safety_checks;
};

#define CASEMATE_DEFAULT_OPTS \
	(struct casemate_options){ \
		.enable_tracing = false, \
		.enable_checking = false, \
		.log_opts = CASEMATE_DEFAULT_LOG_OPTS, \
		.check_opts = CASEMATE_DEFAULT_CHECK_OPTS, \
		.enable_safety_checks = false, \
	}

enum ghost_sysreg_kind {
	SYSREG_VTTBR,
	SYSREG_TTBR_EL2,
	SYSREG_VTCR_EL2,
	SYSREG_TCR_EL2,
	SYSREG_MAIR_EL2,
};

struct casemate_model_step;
typedef int (*vprintf_cb)(void* arg, const char *format, va_list ap);
typedef void* (*sprint_make_buf_cb)(char* arg, u64 n);
typedef void (*sprint_free_buf_cb)(void *buf);
typedef void (*abort_cb)(const char *msg);
typedef u64 (*read_physmem_cb)(u64);
typedef u64 (*read_sysreg_cb)(enum ghost_sysreg_kind sysreg);
typedef void (*trace_cb)(const char *record);

/**
 * struct ghost_driver - Callbacks for driving the casemate model
 *
 * @print: callback for printing, with printf-like arguments.
 * @sprint_create_buffer: callback for making a buffer to pass to driver->print().
 * @sprint_destroy_buffer: frees a buffer created with `sprint_create_buffer`.
 * @halt: callback for failed assertion.
 * @read_physmem: perform a read of memory.
 * @read_sysreg: callback for reading system registers.
 * @trace: tracepoint callback.
 *
 * Casemate is standalone, but sometimes performs side-effects,
 * which must be handled by the parent kernel.
 *
 */
struct ghost_driver {
  vprintf_cb print;
	sprint_make_buf_cb sprint_create_buffer;
	sprint_free_buf_cb sprint_destroy_buffer;
  abort_cb abort;
	read_physmem_cb read_physmem;
	read_sysreg_cb read_sysreg;
	trace_cb trace;
};

#define CASEMATE_DEFAULT_EMPTY_DRIVER \
	(struct ghost_driver){ \
		.print = NULL, \
		.sprint_create_buffer = NULL, \
		.halt = NULL, \
		.read_physmem = NULL, \
		.read_sysreg = NULL, \
		.trace = NULL, \
	}


/**
 * initialise_ghost_cm_driver() - Setup the global ghost driver.
 */
void initialise_ghost_driver(struct ghost_driver *driver);

#endif /* CASEMATE_CONFIG_H */