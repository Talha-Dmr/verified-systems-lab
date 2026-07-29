/*
 * GenMC accepts one C translation unit. Including the implementation keeps
 * this bounded harness tied to exactly the code used by the native tests.
 */
#include "../c/treiber.c"

#include <assert.h>
#include <pthread.h>
#include <stddef.h>

static TreiberStack stack;
static TreiberNode node;

static void *producer(void *unused)
{
    (void)unused;
    node.value = 42;
    node.next = NULL;
    treiber_push(&stack, &node);
    return NULL;
}

static void *consumer(void *unused)
{
    (void)unused;
    TreiberNode *result = treiber_pop(&stack);
    if (result != NULL) {
        assert(result->value == 42);
    }
    return NULL;
}

int main(void)
{
    pthread_t producer_thread;
    pthread_t consumer_thread;

    treiber_init(&stack);
    assert(pthread_create(&producer_thread, NULL, producer, NULL) == 0);
    assert(pthread_create(&consumer_thread, NULL, consumer, NULL) == 0);
    assert(pthread_join(producer_thread, NULL) == 0);
    assert(pthread_join(consumer_thread, NULL) == 0);
    return 0;
}
