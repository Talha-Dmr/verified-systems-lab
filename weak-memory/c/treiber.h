#ifndef WEAK_MEMORY_TREIBER_H
#define WEAK_MEMORY_TREIBER_H

#include <stdbool.h>
#include <stdatomic.h>

/*
 * Nodes are initialized before publication and are never reclaimed or reused.
 * Removing that restriction is a later proof milestone: it introduces ABA and
 * safe-memory-reclamation obligations.
 */
typedef struct TreiberNode {
    int value;
    struct TreiberNode *next;
} TreiberNode;

typedef struct TreiberStack {
    _Atomic(TreiberNode *) head;
} TreiberStack;

void treiber_init(TreiberStack *stack);
void treiber_push(TreiberStack *stack, TreiberNode *node);
TreiberNode *treiber_pop(TreiberStack *stack);
bool treiber_is_empty(const TreiberStack *stack);

#endif
