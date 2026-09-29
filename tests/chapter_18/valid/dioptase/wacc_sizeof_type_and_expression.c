/* Adapted from WACC chapter 17 sizeof/simple.c. Keep both type-name and
 * expression forms of sizeof while using types in the supported C subset. */

int main(void) {
    char byte_value = 'x';
    if (sizeof(int) != 4)
        return 1;
    if (sizeof byte_value != 1)
        return 2;
    return 0;
}
