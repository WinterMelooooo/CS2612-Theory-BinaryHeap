/*#include <stdio.h>
#include<string.h>
#include "smt_lang.tab.h"
#include "smt_lang_flex.h"
#include "smt_lang.h"

int main(int argc, char **argv) {
    
    // char* x1 = "x1";
    // char* x2 = "x2";
    // SmtTerm* t1 = newSmtTerm(SMT_VarName, 0, 0, x1, NULL, NULL, NULL);
    // SmtTerm* t2 = newSmtTerm(SMT_VarName, 0, 0, x2, NULL, NULL, NULL);
    // SmtProp* p = newSmtProp(SMTAT_PROP_EQ, SMT_EQ, NULL, NULL, t1, t2, true);
    // printSmtProp(p);
	char s[80] = "input.txt";
	if(argc == 2)
	{
		printf("manual decided input file\n");
		strcpy(s,argv[1]);
	}
	 
	FILE *fp; // = the file in.
	fp=fopen(s, "rb");
	if (fp == NULL)
	{
		printf("File %s can't be opened.\n", s);
		exit(1);
	}
	else 
	{
		yyin = fp;
	}

	yyparse();
    extern struct SmtProp* root;
	printf("\n PARSING FINISHED. \n");
    
    printSmtProp(root);
    printf("\n");	

	fclose(fp);
}
*/