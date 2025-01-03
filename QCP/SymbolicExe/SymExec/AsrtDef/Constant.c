
#include "Constant.h"

const int Constant_base = 1 << 8;

int Constant_is_zero(struct Constant *c) {
  if (c->size == 1 && c->val[0] == 0) return 1;
  return 0;
}

unsigned long long abs_number_of_Constant(struct Constant *c) {
  if (c -> size > 8 || (c -> size == 8 && c->val[7] > 255)) {
    printf("Constant size is too large\n");
    printf("The constant is: ");
    ConstantPrint(c);
    exit(1);
  }
  unsigned long long number = 0;
  for (int i = c->size - 1; i >= 0 ; --i) {
    number = number * Constant_base + c->val[i];
  }
  return number;
}

struct Constant * Constant_number(unsigned long long number) {
  // printf("Constant value : %llu\n", number);
  struct Constant *c = (struct Constant *)malloc(sizeof(struct Constant));
  c->pos = 1;
  int len = number == 0;
  unsigned long long n = number;
  while (n) {
    n = n / Constant_base;
    len++;
  }
  c->size = len;
  c->val = malloc(len * sizeof(int));
  for (int i = 0; i < len; ++i) 
  {
    c->val[i] = number % Constant_base;
    number = number / Constant_base;
  }
  // ConstantPrint(c);
  return c;
}

struct Constant * Constant_neg(struct Constant * c) {
  // printf("Neg : %d\n", c->pos);
  if (Constant_is_zero(c)) c->pos = 1;
  else c->pos ^= 1;
  // printf("After Neg : %d\n", c->pos);
  return c;
}

struct Constant * Constant_not(struct Constant * c) {
  if (Constant_is_zero(c)) 
  {
    ConstantFree(c);
    return Constant_number(1);
  }
  else {
    ConstantFree(c);
    return Constant_number(0);
  }
}


struct Constant * Constant_nint(struct Constant * c) {
  return Constant_neg(Constant_add(Constant_neg(c), Constant_number(1)));
}

int ConstantAbsCompare(struct Constant * c1, struct Constant * c2) {
  if (c1->size > c2->size) return 1;
  if (c1->size < c2->size) return -1;
  for (int i = c1->size - 1; i >= 0; --i) {
    if (c1->val[i] > c2->val[i]) return 1;
    if (c1->val[i] < c2->val[i]) return -1;
  }
  return 0;
}

struct Constant * Constant_minus(struct Constant * c1, struct Constant * c2) {
  struct Constant *c = (struct Constant *)malloc(sizeof(struct Constant));
  c->pos = c1->pos;
  c->size = c1->size;
  c->val = (int *)malloc(c->size * sizeof(int));
  int borrow = 0;
  for (int i = 0; i < c->size; ++i) {
    int diff = c1->val[i] - borrow;
    if (i < c2->size) diff -= c2->val[i];
    if (diff < 0) {
      diff += Constant_base;
      borrow = 1;
    }
    else borrow = 0;
    c->val[i] = diff;
  }
  while (c->size > 1 && c->val[c->size - 1] == 0) c->size--;
  ConstantFree(c1);
  ConstantFree(c2);
  return c;
}

struct Constant * Constant_add(struct Constant * c1, struct Constant * c2) {
  if (c1 ->pos == c2 -> pos) {
    struct Constant *c = (struct Constant *)malloc(sizeof(struct Constant));
    c -> pos = c1 -> pos;
    c -> size = c1 -> size > c2 -> size ? c1 -> size + 1 : c2 -> size + 1;
    c -> val = (int *)malloc(c -> size * sizeof(int));
    int carry = 0;
    for (int i = 0; i < c -> size; ++i) {
      int sum = carry;
      if (i < c1 -> size) sum += c1 -> val[i];
      if (i < c2 -> size) sum += c2 -> val[i];
      c -> val[i] = sum % Constant_base;
      carry = sum / Constant_base;
    }
    while (c -> size > 1 && c -> val[c -> size - 1] == 0) c -> size--;
    ConstantFree(c1);
    ConstantFree(c2);
    // printf("Result size : %d\n", c -> size);
    return c;
  }
  else {
    if (ConstantAbsCompare(c1, c2) == 1) {
      return Constant_minus(c1, c2);
    }
    else {
      return Constant_minus(c2, c1);
    }
  }
}

struct Constant * Constant_sub(struct Constant * c1, struct Constant * c2) {
  if (c1 -> pos == c2 -> pos) {
    if (ConstantAbsCompare(c1, c2) == 1) {
      return Constant_minus(c1, c2);
    }
    else {
      return Constant_minus(c2, c1);
    }
  }
  else {
    return Constant_add(c1, Constant_neg(c2));
  }
}

struct Constant * Constant_mul(struct Constant * c1, struct Constant * c2) {
  struct Constant *c = (struct Constant *)malloc(sizeof(struct Constant));
  c -> pos = !(c1 -> pos ^ c2 -> pos);
  c -> size = c1 -> size + c2 -> size;
  c -> val = (int *)malloc(c -> size * sizeof(int));
  for (int i = 0; i < c -> size; ++i) c -> val[i] = 0;
  for (int i = 0; i < c1 -> size; ++i) {
    for (int j = 0; j < c2 -> size; ++j) {
      c -> val[i + j] += c1 -> val[i] * c2 -> val[j];
      c -> val[i + j + 1] += c -> val[i + j] / Constant_base;
      c -> val[i + j] %= Constant_base;
    }
  }
  while (c -> size > 1 && c -> val[c -> size - 1] == 0) c -> size--;
  ConstantFree(c1);
  ConstantFree(c2);
  return c;
}

struct Constant * Constant_div(struct Constant * c1, struct Constant * c2) {
  /* TODO: */
  return NULL;
}

struct Constant * Constant_mod(struct Constant * c1, struct Constant * c2) {
  struct Constant *c10 = ConstantDeepCopy(c1);
  struct Constant *c20 = ConstantDeepCopy(c2);
  struct Constant *div_res = Constant_div(c10, c20);
  struct Constant *mul_res = Constant_mul(div_res, c2);
  return Constant_sub(c1, mul_res);
}

// 将高精度整数转换成补码表示
struct Constant * toTwosComplement(struct Constant *a, int size) {
    int *d = (int *)malloc(size * sizeof(int));
    for (int i = 0; i < a->size; i++) {
        d[i] = a->val[i];
    }
    for (int i = a->size; i < size; i++) {
        d[i] = 0;
    }
    free(a->val);
    a->val = d;
    a->size = size;
    if (a->pos == 0) { // 负数转换成补码
        int carry = 1;
        for (int i = a->size - 1; i >= 0; i--) {
            a->val[i] = ~a->val[i];  // 取反操作
            a->val[i] += carry;      // 加 1 操作
            if (a->val[i] != 0) {
                carry = 0;
            }
        }
    }
    return a;
}

// 将补码转换回原来的表示形式
struct Constant * fromTwosComplement(struct Constant *a) {
    if (a->pos == 0) { // 如果是负数，进行补码还原
        int carry = 1;
        for (int i = a->size - 1; i >= 0; i--) {
            a->val[i] -= carry;
            if (a->val[i] == 0xFF && carry == 1) {
                carry = 1;
            } else {
                carry = 0;
            }
            a->val[i] = ~a->val[i];  // 取反操作
        }
    }
    while (a->size > 1 && a->val[a->size - 1] == 0) a->size--;
    return a;
}

struct Constant * Constant_and(struct Constant * c1, struct Constant * c2) {
  struct Constant *c = (struct Constant *)malloc(sizeof(struct Constant));
  c -> pos = c1 -> pos | c2 -> pos;
  c -> size = c1 -> size > c2 -> size ? c1 -> size : c2 -> size;
  c -> val = (int *)malloc(c -> size * sizeof(int));
  c1 = toTwosComplement(c1, c -> size);
  c2 = toTwosComplement(c2, c -> size);
  for (int i = 0; i < c -> size; ++i) {
    c -> val[i] = c1 -> val[i] & c2 -> val[i];
  }
  return fromTwosComplement(c);
}

struct Constant * Constant_or(struct Constant * c1, struct Constant * c2) {
  struct Constant *c = (struct Constant *)malloc(sizeof(struct Constant));
  c -> pos = c1 -> pos & c2 -> pos;
  c -> size = c1 -> size > c2 -> size ? c1 -> size : c2 -> size;
  c -> val = (int *)malloc(c -> size * sizeof(int));
  c1 = toTwosComplement(c1, c -> size);
  c2 = toTwosComplement(c2, c -> size);
  for (int i = 0; i < c -> size; ++i) {
    c -> val[i] = c1 -> val[i] | c2 -> val[i];
  }
  return fromTwosComplement(c);
}

struct Constant * Constant_xor(struct Constant * c1, struct Constant * c2) {
  struct Constant *c = (struct Constant *)malloc(sizeof(struct Constant));
  c -> pos = c1 -> pos ^ c2 -> pos;
  c -> size = c1 -> size > c2 -> size ? c1 -> size : c2 -> size;
  c -> val = (int *)malloc(c -> size * sizeof(int));
  c1 = toTwosComplement(c1, c -> size);
  c2 = toTwosComplement(c2, c -> size);
  for (int i = 0; i < c -> size; ++i) {
    c -> val[i] = c1 -> val[i] ^ c2 -> val[i];
  }
  return fromTwosComplement(c);
}

struct Constant * Constant_shl(struct Constant * c1, struct Constant * c2) {
  if (c2 -> size != 1) {
    printf("The second parameter of shl is two large\n");
    printf("The size is %d\n", c2 -> size);
    printf("The value is %c%llu\n", c2->pos == 1 ? ' ' : '-', abs_number_of_Constant(c2));
    exit(1);
  }
  if (c2 -> pos == 0) {
    printf("The second parameter of shl is negative\n");
    exit(1);
  }
  // printf("SHL : %d\n", c1->pos);
  struct Constant *c = (struct Constant *)malloc(sizeof(struct Constant));
  c -> pos = c1 -> pos;
  int byteshift = c2 -> val[0] / 8;
  int bitshift = c2 -> val[0] % 8;
  c -> size = c1 -> size + byteshift + 1;
  c -> val = (int *)malloc(c -> size * sizeof(int));
  for (int i = 0; i < c -> size; ++i) c -> val[i] = 0;
  for (int i = 0; i < c1 -> size; ++i) {
    c -> val[i + byteshift] |= c1 -> val[i] << bitshift;
    c -> val[i + byteshift + 1] |= c1 -> val[i] >> (8 - bitshift);
  }
  return c;
}

struct Constant * Constant_shr(struct Constant * c1, struct Constant * c2) {
  if (c2 -> size != 1) {
    printf("The second parameter of shr is two large\n");
    exit(1);
  }
  if (c2 -> pos == 0) {
    printf("The second parameter of shr is negative\n");
    exit(1);
  }
  struct Constant *c = (struct Constant *)malloc(sizeof(struct Constant));
  c -> pos = c1 -> pos;
  int byteshift = c2 -> val[0] / 8;
  int bitshift = c2 -> val[0] % 8;
  c -> size = c1 -> size - byteshift;
  c -> val = (int *)malloc(c -> size * sizeof(int));
  for (int i = 0; i < c -> size; ++i) c -> val[i] = 0;
  for (int i = 0; i < c -> size; ++i) {
    c -> val[i] |= c1 -> val[i + byteshift] >> bitshift;
    c -> val[i] |= c1 -> val[i + byteshift + 1] << (8 - bitshift);
  }
  if (c -> pos == 0) {
    int signByte = 0xFF; 
    for (int i = c -> size - 1; i >= 0; --i) {
      c -> val[i] |= signByte << (8 - bitshift);
      signByte = signByte >> (8 - bitshift);
    }
  }
  return c;
}

struct Constant * Constant_ZPOW(struct Constant *c1, struct Constant *c2) {
  struct Constant *c = Constant_number(1);
  struct Constant *cnow = ConstantDeepCopy(c1);
  for (int i = 0; i < c2 -> size; ++i) {
    for (int j = 0; j < 8; ++j) {
      if (c2 -> val[i] & (1 << j)) {
        c = Constant_mul(c, ConstantDeepCopy(cnow));
      }
      cnow = Constant_mul(cnow, ConstantDeepCopy(cnow));
    }
  }
  return c;
}

struct Constant * Constant_LNB(struct Constant *c1, struct Constant *c2) {
  if (c2 -> pos == 0) {
    printf("The second parameter of LNB is negative\n");
    exit(1);
  }
  if (c2 -> size != 1) {
    printf("The second parameter of LNB is too large\n");
    exit(1);
  }
  struct Constant *c = (struct Constant *)malloc(sizeof(struct Constant));
  c->pos = c1->pos;
  c->size = c2->val[0] / 8;
  c->val = (int *)malloc(c->size * sizeof(int));
  c1 = toTwosComplement(c1, c->size);
  for (int i = 0; i < c->size; ++i) c->val[i] = c1->val[i];
  return fromTwosComplement(c);
}

struct Constant *Constant_ULNB(struct Constant *c1, struct Constant *c2) {
  if (c2 -> pos == 0) {
    printf("The second parameter of ULNB is negative\n");
    exit(1);
  }
  if (c2 -> size != 1) {
    printf("The second parameter of ULNB is too large\n");
    exit(1);
  }
  struct Constant *c = (struct Constant *)malloc(sizeof(struct Constant));
  // printf("ULNB : %d\n", c1->pos);
  c->pos = 1;
  c->size = c2->val[0] / 8;
  c->val = (int *)malloc(c->size * sizeof(int));
  c1 = toTwosComplement(c1, c->size);
  for (int i = 0; i < c->size; ++i) c->val[i] = c1->val[i];
  // printf("ULNB : %d\n", c->pos);
  return c;
}

struct Constant * ConstantDeepCopy(struct Constant *c) {
  struct Constant *cnew = (struct Constant *)malloc(sizeof(struct Constant));
  cnew -> pos = c -> pos;
  cnew -> size = c -> size;
  cnew -> val = (int *)malloc(c -> size * sizeof(int));
  for (int i = 0; i < c -> size; ++i) {
    cnew -> val[i] = c -> val[i];
  }
  return cnew;
}

void ConstantPrint(struct Constant * c) {
  if (c == NULL) {
    printf("NULL\n");
    return;
  }
  if (c -> size <= 0) {
    printf("Error !!!!\n");
    printf("The constant size is %d\n", c -> size);
    exit(1);
  }
  if (c -> pos == 0) printf("-");
  printf("0x");
  for (int i = c -> size - 1; i >= 0; --i) {
    printf("%02X", c -> val[i]);
  }
  printf("\n");
}

void ConstantFree(struct Constant *c) {
  if (c == NULL) return;
  free(c -> val);
  free(c);
}