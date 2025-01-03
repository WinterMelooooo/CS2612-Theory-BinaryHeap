#include "plang.h"
#include "env.h"

void parse_program(FILE *,
                   void (*k)(struct partial_program *, struct environment *),
                   struct environment *env);
void parse_program_path(char *,
                        void (*k)(struct partial_program *, struct environment *),
                        struct environment *env);
