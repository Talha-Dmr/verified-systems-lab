/*
 * GenMC accepts one C translation unit. Including the implementation keeps
 * this bounded Relinche harness tied to exactly the code used by the native
 * tests and the other GenMC harnesses.
 */
#include "../c/treiber.c"

#include <assert.h>
#include <genmc.h>
#include <pthread.h>
#include <stddef.h>

static TreiberStack stack;
static TreiberNode node;

static void *push_once(void *unused)
{
    (void)unused;

    __VERIFIER_method_begin("push", 101);
    treiber_push(&stack, &node);
    __VERIFIER_method_end("push", 0);
    return NULL;
}

static void *pop_once(void *unused)
{
    (void)unused;

    __VERIFIER_method_begin("pop", 0);
    TreiberNode *result = treiber_pop(&stack);
    int value = result == NULL ? 0 : result->value;
    __VERIFIER_method_end("pop", value);
    return NULL;
}

int main(void)
{
    pthread_t push_thread;
    pthread_t pop_thread;

    __VERIFIER_method_begin("init_stack", 0);
    treiber_init(&stack);
    __VERIFIER_method_end("init_stack", 0);
    node.value = 101;
    node.next = NULL;

    assert(pthread_create(&push_thread, NULL, push_once, NULL) == 0);
    assert(pthread_create(&pop_thread, NULL, pop_once, NULL) == 0);
    assert(pthread_join(push_thread, NULL) == 0);
    assert(pthread_join(pop_thread, NULL) == 0);
    __VERIFIER_method_begin("clear_stack", 0);
    __VERIFIER_method_end("clear_stack", 0);
    return 0;
}
