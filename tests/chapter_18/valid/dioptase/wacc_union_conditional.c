/*
 * Adapted from WACC chapter_18/valid/extra_credit/union_copy/unions_in_conditionals.c.
 * Replace one use of unsupported long with int. The union conditional expression and both result assertions remain unchanged.
 */
// Like structures, unions can appear in conditional expression

union u {
    int l;
    int i;
    char c;
};
int choose_union(int flag) {
    union u one;
    union u two;
    one.l = -1;
    two.i = 100;

    return (flag ? one : two).c;
}

int main(void) {
    if (choose_union(1) != -1) {
        return 1; // fail
    }

    if (choose_union(0) != 100) {
        return 2; // fail
    }

    return 0; // success
}