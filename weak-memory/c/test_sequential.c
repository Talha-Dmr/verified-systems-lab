#include "treiber.h"

#include <assert.h>
#include <stdio.h>

int main(void)
{
    TreiberStack stack;
    TreiberNode first = {.value = 10, .next = NULL};
    TreiberNode second = {.value = 20, .next = NULL};
    TreiberNode third = {.value = 30, .next = NULL};

    treiber_init(&stack);
    assert(treiber_is_empty(&stack));

    treiber_push(&stack, &first);
    treiber_push(&stack, &second);
    treiber_push(&stack, &third);

    assert(treiber_pop(&stack) == &third);
    assert(treiber_pop(&stack) == &second);
    assert(treiber_pop(&stack) == &first);
    assert(treiber_pop(&stack) == NULL);
    assert(treiber_is_empty(&stack));

    puts("sequential: LIFO and empty-stack checks passed");
    return 0;
}
