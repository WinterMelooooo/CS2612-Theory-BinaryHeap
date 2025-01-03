#include "utils.h"

unsigned long long build_nat(char *c, int len) {
  unsigned long long s = 0;
  int i = 0;
  for (i = 0; i < len && c[i] != 'l' && c[i] != 'u'; ++i) {
    /* 18446744073709551615 */
    if (s > 1844674407370955161ull ||
        (s == 1844674407370955161ull && c[i] - '0' > 5)) {
      failwith("Integer literal is too large");
    }
    s = s * 10 + (c[i] - '0');
  }
  /* if (Signed == 0 && type == 0 && s > 2147483648u) { */
  /*   failwith("Integer literal is too large for signed int"); */
  /* } */
  /* if (Signed == 0 && type == 1 && s > 9223372036854775808ull) { */
  /*   failwith("Integer literal is too large for signed long long"); */
  /* } */
  /* if (Signed == 1 && type == 0 && s > 4294967295u) { */
  /*   failwith("Integer literal is too large for unsigned int"); */
  /* } */
  /* if (Signed == 1 && type == 1 && s > 18446744073709551615ull) { */
  /*   failwith("Integer literal is too large for unsigned long long"); */
  /* } */
  return s;
}

unsigned long long build_hex(char *c, int len) {
  unsigned long long s = 0;
  int i = 0;
  for (i = 0; i < len && c[i] != 'l' && c[i] != 'u'; ++i) {
    /* 18446744073709551615 */
    if (s > 1152921504606846975) {
      failwith("Integer literal is too large");
    }
    s *= 16;
    if ('0' <= c[i] && c[i] <= '9')
      s += c[i] - '0';
    else if ('a' <= c[i] && c[i] <= 'f')
      s += c[i] - 'a' + 10;
    else
      s += c[i] - 'A' + 10;
  }
  return s;
}


char *new_str(char *str, int len) {
  char *res = (char *)malloc(sizeof(char) * (len + 1));
  if (res == NULL) {
    fprintf(stderr, "Failure in malloc.\n");
    exit(0);
  }
  strcpy(res, str);
  res[len] = '\0';
  return res;
}

char *new_identifier(char *str, int len) {
  int real_len = 0;
  char *i, *j;
  int l = 0;
  for (i = str; l < len; i++, l++) {
    real_len++;
    if (*i == ':') {
      i++;
      l++;
    }
  }
  char *res = (char *)malloc(sizeof(char) * (real_len + 1));
  if (res == NULL) {
    fprintf(stderr, "Failure in malloc.\n");
    exit(0);
  }
  for (i = res, j = str, l = 0; l < len; i++, j++, l++) {
    if (*j == ':') {
      *i = '.';
      j++;
      l++;
    } else {
      *i = *j;
    }
  }
  res[real_len] = '\0';
  return res;
}

char *clone_str(char *str) {
  if (str == NULL)
    return NULL;
  int len = strlen(str);
  char *res;
  res = (char *)malloc(sizeof(char) * (len + 1));
  if (res == NULL) {
    fprintf(stderr, "Failure in malloc.\n");
    exit(0);
  }
  strcpy(res, str);
  return res;
}

char *embed_str(char *fmt, char *str) {
  int len_fmt = strlen(fmt);
  int len_str = strlen(str);
  char *res = (char *)malloc(sizeof(char) * (len_fmt + len_str - 2 + 1));
  sprintf(res, fmt, str);
  return res;
}

char *embed_int(char *fmt, int n) {
  int len_fmt = strlen(fmt);
  int len_int;
  if (n == 0)
    len_int = 1;
  else {
    int t = n;
    len_int = 0;
    while (t != 0) {
      len_int += 1;
      t -= 1;
    }
  }
  char *res = (char *)malloc(sizeof(char) * (len_fmt + len_int - 2 + 1));
  sprintf(res, fmt, n);
  return res;
}

void print_escaped_str_File(FILE *f, char *str) {
  for (; *str != '\0'; str++) {
    char c = *str;
    switch (c) {
    case '\n': fprintf(f,"\\n"); break;
    case '\t': fprintf(f,"\\t"); break;
    case '\"': fprintf(f,"\\\""); break;
    case '\'': fprintf(f,"\\\'"); break;
    case '\\': fprintf(f,"\\\\"); break;
    case '\?': fprintf(f,"\\\?"); break;
    default: fprintf(f,"%c",c); break;
    }
  }
}

void print_escaped_str(char *str) {
  print_escaped_str_File(stdout, str);
}

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpointer-to-int-cast"
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wint-to-pointer-cast"

int cast_void(void *x) {
  return (int)x;
}

void *cast_int(int x) {
  return (void *)x;
}

#pragma GCC diagnostic pop
#pragma GCC diagnostic pop

int roundup(int x, int gran) {
  if (x % gran == 0)
    return x;
  return (x / gran) * gran + gran;
}

void print_subscript_aux(unsigned int x) {
  char *sub[] = {"₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉"};
  if (x == 0)
    return;
  print_subscript_aux(x / 10);
  printf("%s", sub[x % 10]);
}

void print_subscript(unsigned int x) {
  if (x == 0)
    printf("₀");
  else
    print_subscript_aux(x);
}

char *find_file_in_same_dir(char *file, char *relative) {
  int filelen = strlen(file);
  int relativelen = strlen(relative);
  char *new = (char *)malloc((filelen + relativelen) * sizeof(char));
  int i;
  for (i = filelen - 1; i >= 0 && file[i] != '/'; i -= 1)
    ;
  while (i >= 1 && file[i-1] == '/')
    i -= 1;
  i += 1;
  strcpy(new, file);
  strcpy(new + i, relative);
  return new;
}

#include "../SymExec/Utility/List.h"
extern struct StringList *additional_search_path;

char *find_file_in_search_path(char *file, char *relative) {
  if (relative[0] == '/')
    return relative;

  char *same_dir = find_file_in_same_dir(file, relative);
  FILE *fp = fopen(same_dir, "r");
  if (fp != NULL) {
    fclose(fp);
    return same_dir;
  }

  struct StringListNode *i;
  for (i = additional_search_path->head; i != NULL; i = i->next) {
    char *path = find_file_in_same_dir(i->data, relative);
    FILE *fp = fopen(path, "r");
    if (fp != NULL) {
      fclose(fp);
      return path;
    }
    free(path);
  }
  failwith("No such file %s in search path", relative);
}
