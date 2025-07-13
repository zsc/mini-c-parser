# Makefile for testing the compiler against the c-testsuite

# --- Configuration ---

# Remote host for lli execution
REMOTE_HOST := ombp
# Path to the C test suite
TEST_SUITE_PATH := ../c-testsuite/tests/single-exec

# --- Auto-discovery of Test Files ---

# Find all .c files in the test suite directory
C_SOURCES := $(wildcard $(TEST_SUITE_PATH)/*.c)

# Create a directory to store results and logs
RESULTS_DIR := test_results
# Define target log files for each source file
LOG_FILES := $(patsubst $(TEST_SUITE_PATH)/%.c,$(RESULTS_DIR)/%.c.log,$(C_SOURCES))

# Compiler executable
COMPILER_EXE := _build/default/bin/main.exe

# --- Main Targets ---

# Default target: build, run tests, and show report
.PHONY: all
all: report

# Build the compiler first. This target is used as a dependency.
.PHONY: dune-build
dune-build:
	@echo "--- Building compiler with Dune ---"
	@dune build

# Run all tests by ensuring all log files are created.
# The '-j' flag will be used here by the user.
.PHONY: test
test: dune-build $(LOG_FILES)

# Generate a summary report from the log files.
.PHONY: report
report: test
	@echo
	@echo "================================================================================="
	@echo "                            TEST RESULTS SUMMARY"
	@echo "================================================================================="
	@printf "%-45s | %-12s | %-15s\n" "Test Case" "Result" "Time (s)"
	@echo "---------------------------------------------+--------------+-----------------"
	
	# Step 1: Extract data for each test, format it, and pipe ONLY this data to sort.
	# This awk script has no BEGIN or END block.
	@awk ' \
		{ \
			if ($$1 == "Test:")   { test_case = $$2 } \
			if ($$1 == "Result:") { result = $$2 } \
			if ($$1 == "Time:")   { time = $$2; printf "%-45s | %-12s | %-15s\n", test_case, result, time; } \
		} \
	' $(LOG_FILES) | sort
	
	# Step 2: Read the log files again to calculate and print the final summary.
	# This awk script does the counting and prints the footer in its END block.
	@awk ' \
		BEGIN { \
			success=0; total=0; \
		} \
		{ \
			if ($$1 == "Result:" && $$2 == "SUCCESS") { success++ } \
			if ($$1 == "Time:") { total++ } \
		} \
		END { \
			print "================================================================================="; \
			printf " Done. Total: %d, Passed: %d, Failed: %d\n", total, success, total-success; \
			print "================================================================================="; \
		}' $(LOG_FILES)

# Clean up all generated files
.PHONY: clean
clean:
	@echo "--- Cleaning up generated files ---"
	@rm -rf $(RESULTS_DIR)

# --- Pattern Rule for a Single Test ---

# This rule defines how to process a single .c file.
# It depends on the source .c file and the compiler being built.
# The command is prefixed with '-' to ensure 'make' continues even if a test fails.
$(RESULTS_DIR)/%.c.log: $(TEST_SUITE_PATH)/%.c dune-build
	-@mkdir -p $(@D)
	@echo "--- Testing $< ---"
	@( \
		START_TIME=$$(date +%s.%N); \
		TEST_NAME=$$(basename $<); \
		LL_FILE=$(RESULTS_DIR)/$${TEST_NAME}.ll; \
		REMOTE_LL_PATH=sandbox/$${TEST_NAME}.ll; \
		LOG_FILE=$@; \
		\
		echo "Test: $${TEST_NAME}" > $${LOG_FILE}; \
		\
		$(COMPILER_EXE) < $< > $${LL_FILE} 2>/dev/null; \
		COMPILER_EC=$$?; \
		if [ $${COMPILER_EC} -ne 0 ] || [ ! -s "$${LL_FILE}" ]; then \
			echo "Result: FAILURE (Compilation)" >> $${LOG_FILE}; \
		else \
			scp -q $${LL_FILE} $(REMOTE_HOST):~/sandbox/ >/dev/null 2>&1; \
			SCP_EC=$$?; \
			if [ $${SCP_EC} -ne 0 ]; then \
				echo "Result: FAILURE (SCP)" >> $${LOG_FILE}; \
			else \
				ssh $(REMOTE_HOST) "lli ~/$${REMOTE_LL_PATH}" >/dev/null 2>&1; \
				LLI_EC=$$?; \
				if [ $${LLI_EC} -eq 1 ] || [ $${LLI_EC} -ge 128 ]; then \
					echo "Result: FAILURE (LLI Error $${LLI_EC})" >> $${LOG_FILE}; \
				else \
					echo "Result: SUCCESS" >> $${LOG_FILE}; \
				fi; \
				ssh $(REMOTE_HOST) "rm -f ~/$${REMOTE_LL_PATH}" >/dev/null 2>&1; \
			fi; \
		fi; \
		\
		END_TIME=$$(date +%s.%N); \
		DURATION=$$(echo "$$END_TIME - $$START_TIME" | bc); \
		printf "Time: %.4f\n" $${DURATION} >> $${LOG_FILE}; \
		\
		rm -f $${LL_FILE}; \
	)
