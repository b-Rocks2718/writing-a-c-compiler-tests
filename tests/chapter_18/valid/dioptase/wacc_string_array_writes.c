/*
 * Adapted from WACC chapter_16/valid/strings_as_initializers/write_to_array.c.
 * Check the same printed strings in memory because the emulator CRT has no puts.
 */
#define TEST_OK 0
#define BAD_INITIAL_ARRAY 1
#define BAD_UPDATED_ARRAY 2
#define BAD_FIRST_NESTED_ARRAY 3
#define BAD_SECOND_NESTED_ARRAY 4
#define BAD_UPDATED_NESTED_ARRAY 5

int same_string(const char *left, const char *right) {
    while (*left && *right) {
        if (*left != *right)
            return 0;
        left = left + 1;
        right = right + 1;
    }
    return *left == *right;
}

int main(void) {
    char flat_arr[4] = "abc";
    if (!same_string(flat_arr, "abc"))
        return BAD_INITIAL_ARRAY;

    flat_arr[2] = 'x';
    if (!same_string(flat_arr, "abx"))
        return BAD_UPDATED_ARRAY;

    char nested_array[2][6] = {"Hello", "World"};
    if (!same_string(nested_array[0], "Hello"))
        return BAD_FIRST_NESTED_ARRAY;
    if (!same_string(nested_array[1], "World"))
        return BAD_SECOND_NESTED_ARRAY;

    nested_array[0][0] = 'J';
    if (!same_string(nested_array[0], "Jello"))
        return BAD_UPDATED_NESTED_ARRAY;
    return TEST_OK;
}
