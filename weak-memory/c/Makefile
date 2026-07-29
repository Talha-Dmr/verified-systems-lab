CC ?= cc
CPPFLAGS ?=
CFLAGS ?= -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror
LDFLAGS ?=
LDLIBS ?= -pthread

BUILD_DIR := ../build/c
COMMON_OBJECT := $(BUILD_DIR)/treiber.o
TESTS := $(BUILD_DIR)/test_sequential $(BUILD_DIR)/test_stress

.PHONY: all test clean

all: $(TESTS)

test: all
	$(BUILD_DIR)/test_sequential
	$(BUILD_DIR)/test_stress

$(BUILD_DIR):
	mkdir -p $@

$(COMMON_OBJECT): treiber.c treiber.h | $(BUILD_DIR)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

$(BUILD_DIR)/test_sequential: test_sequential.c $(COMMON_OBJECT) treiber.h
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(COMMON_OBJECT) $(LDFLAGS) $(LDLIBS) -o $@

$(BUILD_DIR)/test_stress: test_stress.c $(COMMON_OBJECT) treiber.h
	$(CC) $(CPPFLAGS) $(CFLAGS) $< $(COMMON_OBJECT) $(LDFLAGS) $(LDLIBS) -o $@

clean:
	rm -rf $(BUILD_DIR)
