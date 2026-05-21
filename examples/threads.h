#ifndef THREADS_H
#define THREADS_H

/* some platforms (macOS) do not distribute c11-compatible threads.h with clang
 * even with -std=c11
 *
 * so here's a dumb wrapper around pthread to use instead */

#ifndef CONFIG_HAS_THREADS

#include <pthread.h>
#include <sched.h>
#include <stdlib.h>

typedef pthread_t thrd_t;
typedef int (*thrd_start_t)(void *);
typedef pthread_mutex_t mtx_t;

#define thrd_success 0
#define thrd_error 1

#define mtx_plain 0

struct thrd_start_ctx {
	thrd_start_t fn;
	void *arg;
};

/* wraps up a thrd_start_t into a pthread-compatible void *(f)(void*) */
static inline void *thrd_start_wrapper(void *arg)
{
	struct thrd_start_ctx *ctx;
	thrd_start_t fn;
	void *fn_arg;

	ctx = arg;
	fn = ctx->fn;
	fn_arg = ctx->arg;

	/* clean up the context now it's not needed */
	free(arg);

	/* Run the wrapped function
	 * thrd fns returns int, but pthread functions return void*
	 * so we wrangle through a type that is guaranteed to be longer than an int and fit in a void*
	 */
	return (void *)(long)fn(fn_arg);
}

static inline int thrd_create(thrd_t *thr, thrd_start_t fn, void *arg)
{
	int ret;
	struct thrd_start_ctx *ctx = malloc(sizeof(struct thrd_start_ctx));

	if (! ctx)
		return thrd_error;

	ctx->fn = fn;
	ctx->arg = arg;

	if (pthread_create(thr, NULL, thrd_start_wrapper, ctx))
		ret = thrd_error;
	else
		ret = thrd_success;

	if (ret == thrd_error)
		free(ctx);

	return ret;
}

static inline int thrd_join(thrd_t thr, int *res)
{
	void *ret;

	if (pthread_join(thr, &ret))
		return thrd_error;

	if (res)
		*res = (int)(long)ret;

	return thrd_success;
}

static inline thrd_t thrd_current(void)
{
	return pthread_self();
}

static inline int thrd_equal(thrd_t lhs, thrd_t rhs)
{
	return pthread_equal(lhs, rhs);
}

static inline void thrd_yield(void)
{
	sched_yield();
}

static inline int mtx_init(mtx_t *mutex, int type)
{
	if (pthread_mutex_init(mutex, NULL))
		return thrd_error;
	else
		return thrd_success;
}

static inline int mtx_lock(mtx_t *mutex)
{
	if (pthread_mutex_lock(mutex))
		return thrd_error;
	else
		return thrd_success;
}

static inline int mtx_unlock(mtx_t *mutex)
{
	if (pthread_mutex_unlock(mutex))
		return thrd_error;
	else
		return thrd_success;
}

#else /* CONFIG_HAS_THREADS */
#include_next <threads.h>
#endif /* CONFIG_HAS_THREADS */

#endif /* THREADS_H */
