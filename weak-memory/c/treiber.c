#include "treiber.h"

#include <stddef.h>

void treiber_init(TreiberStack *stack)
{
    atomic_init(&stack->head, NULL);
}

void treiber_push(TreiberStack *stack, TreiberNode *node)
{
    TreiberNode *observed =
        atomic_load_explicit(&stack->head, memory_order_relaxed);

    do {
        node->next = observed;
    } while (!atomic_compare_exchange_weak_explicit(
        &stack->head,
        &observed,
        node,
        memory_order_release,
        memory_order_relaxed));
}

TreiberNode *treiber_pop(TreiberStack *stack)
{
    TreiberNode *observed =
        atomic_load_explicit(&stack->head, memory_order_acquire);

    while (observed != NULL) {
        TreiberNode *next = observed->next;

        if (atomic_compare_exchange_weak_explicit(
                &stack->head,
                &observed,
                next,
                memory_order_acquire,
                memory_order_acquire)) {
            return observed;
        }
    }

    return NULL;
}

bool treiber_is_empty(const TreiberStack *stack)
{
    return atomic_load_explicit(&stack->head, memory_order_acquire) == NULL;
}
