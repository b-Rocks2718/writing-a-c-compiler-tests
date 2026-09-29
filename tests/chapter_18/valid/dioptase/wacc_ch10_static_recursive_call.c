/*
 * Adapted from WACC chapter_10/valid/static_recursive_call.c.
 * Capture the original putchar side effects in memory and check every byte.
 * The Dioptase emulator CRT has no stdout service; the original program's
 * return value and control flow remain under test.
 */
#define WACC_EXPECTED_RETURN 0
#define WACC_EXPECTED_LENGTH 26
#define WACC_TEST_OK 0
#define WACC_BAD_RETURN 1
#define WACC_BAD_OUTPUT 2

static char wacc_captured_output[WACC_EXPECTED_LENGTH];
static int wacc_captured_length;
static int wacc_output_overflow;

int wacc_emit_char(int c) {
    if (wacc_captured_length == WACC_EXPECTED_LENGTH) {
        wacc_output_overflow = 1;
    } else {
        wacc_captured_output[wacc_captured_length] = (char)c;
        wacc_captured_length = wacc_captured_length + 1;
    }
    return c;
}

// Test updating a static local variable over multiple function invocations;
// also test passing a static variable as an argument

int print_alphabet(void) {
    /* the value of count increases by 1
     * each time we call print_alphabet()
     */
    static int count = 0;
    wacc_emit_char(count + 65); // 65 is ASCII 'A'
    count = count + 1;
    if (count < 26) {
        print_alphabet();
    }
    return count;
}

int wacc_program_main(void) {
    print_alphabet();
    // The source main implicitly returned zero; preserve that after wrapping.
    return WACC_EXPECTED_RETURN;
}

int main(void) {
    const char *expected_output = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    int original_result = wacc_program_main();
    if (original_result != WACC_EXPECTED_RETURN)
        return WACC_BAD_RETURN;
    if (wacc_output_overflow || wacc_captured_length != WACC_EXPECTED_LENGTH)
        return WACC_BAD_OUTPUT;
    for (int i = 0; i < WACC_EXPECTED_LENGTH; i = i + 1) {
        if (wacc_captured_output[i] != expected_output[i])
            return WACC_BAD_OUTPUT;
    }
    return WACC_TEST_OK;
}
