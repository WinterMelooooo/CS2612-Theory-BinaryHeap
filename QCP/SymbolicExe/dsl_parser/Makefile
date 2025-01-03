lexer.c : lexer.l 
		   flex lexer.l 
parser.c : parser.y
		   bison -o parser.c -d -v parser.y
lang.o : lang.c lang.h
		   gcc -c lang.c