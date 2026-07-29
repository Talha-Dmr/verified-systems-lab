/*
 * GenMC accepts one C translation unit. Including the implementation keeps
 * this bounded harness tied to exactly the code used by the native tests.
 */
#include "../c/treiber.c"

#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>

static TreiberStack stack;
static TreiberNode nodes[2];
static _Atomic(TreiberNode *) results[2];

static void *push_then_pop(void *argument)
{
    int id = *(int *)argument;
    nodes[id].value = id + 1;
    nodes[id].next = NULL;

    treiber_push(&stack, &nodes[id]);
    TreiberNode *result = treiber_pop(&stack);
    atomic_store_explicit(&results[id], result, memory_order_relaxed);
    return NULL;
}

int main(void)
{
    pthread_t threads[2];
    int ids[2] = {0, 1};

    treiber_init(&stack);
    atomic_init(&results[0], NULL);
    atomic_init(&results[1], NULL);

    assert(pthread_create(&threads[0], NULL, push_then_pop, &ids[0]) == 0);
    assert(pthread_create(&threads[1], NULL, push_then_pop, &ids[1]) == 0);
    assert(pthread_join(threads[0], NULL) == 0);
    assert(pthread_join(threads[1], NULL) == 0);

    TreiberNode *first =
        atomic_load_explicit(&results[0], memory_order_relaxed);
    TreiberNode *second =
        atomic_load_explicit(&results[1], memory_order_relaxed);

    assert(first != NULL);
    assert(second != NULL);
    assert(first != second);
    assert(treiber_is_empty(&stack));
    return 0;
}
