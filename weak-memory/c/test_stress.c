#include "treiber.h"

#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

enum {
    THREAD_COUNT = 4,
    OPERATIONS_PER_THREAD = 20000,
    NODE_COUNT = THREAD_COUNT * OPERATIONS_PER_THREAD
};

typedef struct WorkerArgs {
    int thread_id;
} WorkerArgs;

static TreiberStack stack;
static TreiberNode nodes[NODE_COUNT];
static _Atomic unsigned char seen[NODE_COUNT];
static atomic_bool start_requested;
static atomic_bool failed;

static void record_pop(TreiberNode *node)
{
    int value = node->value;

    if (value < 0 || value >= NODE_COUNT) {
        atomic_store_explicit(&failed, true, memory_order_relaxed);
        return;
    }

    unsigned char previous =
        atomic_exchange_explicit(&seen[value], 1, memory_order_relaxed);
    if (previous != 0) {
        atomic_store_explicit(&failed, true, memory_order_relaxed);
    }
}

static void *worker(void *raw_args)
{
    WorkerArgs *args = raw_args;
    int first_index = args->thread_id * OPERATIONS_PER_THREAD;

    while (!atomic_load_explicit(&start_requested, memory_order_acquire)) {
    }

    for (int offset = 0; offset < OPERATIONS_PER_THREAD; ++offset) {
        int index = first_index + offset;
        nodes[index].value = index;
        nodes[index].next = NULL;
        treiber_push(&stack, &nodes[index]);

        TreiberNode *popped;
        do {
            popped = treiber_pop(&stack);
        } while (popped == NULL);

        record_pop(popped);
    }

    return NULL;
}

int main(void)
{
    pthread_t threads[THREAD_COUNT];
    WorkerArgs args[THREAD_COUNT];

    treiber_init(&stack);
    atomic_init(&start_requested, false);
    atomic_init(&failed, false);
    for (int index = 0; index < NODE_COUNT; ++index) {
        atomic_init(&seen[index], 0);
    }

    for (int thread = 0; thread < THREAD_COUNT; ++thread) {
        args[thread].thread_id = thread;
        if (pthread_create(&threads[thread], NULL, worker, &args[thread]) != 0) {
            perror("pthread_create");
            return EXIT_FAILURE;
        }
    }

    atomic_store_explicit(&start_requested, true, memory_order_release);

    for (int thread = 0; thread < THREAD_COUNT; ++thread) {
        if (pthread_join(threads[thread], NULL) != 0) {
            perror("pthread_join");
            return EXIT_FAILURE;
        }
    }

    for (int index = 0; index < NODE_COUNT; ++index) {
        if (atomic_load_explicit(&seen[index], memory_order_relaxed) != 1) {
            atomic_store_explicit(&failed, true, memory_order_relaxed);
        }
    }

    if (!treiber_is_empty(&stack)) {
        atomic_store_explicit(&failed, true, memory_order_relaxed);
    }

    if (atomic_load_explicit(&failed, memory_order_relaxed)) {
        fputs("stress: duplicate, missing, invalid, or leftover node\n", stderr);
        return EXIT_FAILURE;
    }

    printf("stress: %d nodes pushed and popped exactly once\n", NODE_COUNT);
    return EXIT_SUCCESS;
}
