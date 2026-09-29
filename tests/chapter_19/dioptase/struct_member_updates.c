/*
 * Check compound assignment and postfix updates on local struct members.
 * Also check that a pointer-producing left side is evaluated once.
 */
#define INITIAL_LOCAL_VALUE 24
#define DIVISOR 3
#define VALUE_AFTER_DIVISION 8
#define VALUE_AFTER_DECREMENT 7
#define INITIAL_GLOBAL_VALUE 20
#define INCREMENT 2
#define VALUE_AFTER_INCREMENT 22
#define VALUE_AFTER_GLOBAL_DECREMENT 21
#define TEST_OK 0
#define BAD_LOCAL_COMPOUND 1
#define BAD_LOCAL_POSTFIX 2
#define BAD_POINTER_COMPOUND 3
#define BAD_POINTER_POSTFIX 4

struct Box {
  int padding;
  int value;
};

struct Box global_box = {0, INITIAL_GLOBAL_VALUE};
int pointer_evaluations;

struct Box *select_box(void) {
  pointer_evaluations++;
  return &global_box;
}

int main(void) {
  struct Box local = {0, INITIAL_LOCAL_VALUE};
  int divided = (local.value /= DIVISOR);
  if (divided != VALUE_AFTER_DIVISION || local.value != VALUE_AFTER_DIVISION)
    return BAD_LOCAL_COMPOUND;

  int old_local = local.value--;
  if (old_local != VALUE_AFTER_DIVISION || local.value != VALUE_AFTER_DECREMENT)
    return BAD_LOCAL_POSTFIX;

  int incremented = (select_box()->value += INCREMENT);
  if (pointer_evaluations != 1 || incremented != VALUE_AFTER_INCREMENT ||
      global_box.value != VALUE_AFTER_INCREMENT)
    return BAD_POINTER_COMPOUND;

  int old_global = select_box()->value--;
  if (pointer_evaluations != 2 || old_global != VALUE_AFTER_INCREMENT ||
      global_box.value != VALUE_AFTER_GLOBAL_DECREMENT)
    return BAD_POINTER_POSTFIX;

  return TEST_OK;
}
