#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void executeMlton (char * fname) {
	char * argv[3];
	argv[0] = "/Users/HeZhu/Downloads/mlton-20100608/build/bin/mlton";
	char * smlfilename = (char*) malloc (strlen(fname) + 5);
	strcpy (smlfilename, fname);
	strcpy (smlfilename + strlen(fname), ".mlb");
	strcpy (smlfilename + strlen(fname) + 4, "\0");
	argv[1] = smlfilename;
	argv[2] = NULL;
	
	pid_t pid;	
	int status;
	if((pid = fork()) < 0)
	{
	  printf("an error occurred while forking process to compile binary version of user program\n");
	}
	else if(pid == 0)
	{
	  /* this is the child */
	  execv("/Users/HeZhu/Downloads/mlton-20100608/build/bin/mlton", argv);
	  printf("if this line is printed then compiling user program failed\n");
	}
	else
	{
	  /* this is the parent */
	  wait(&status);
	  printf("compiling user program succeed!\n");
	}
	
	free(smlfilename);
}

void executeProgram (char * fname) {
	char * argv[2];
	argv[0] = fname;
	argv[1] = NULL;

	pid_t pid;	
	int status;
	if((pid = fork()) < 0)
	{
	  printf("an error occurred while forking process to execute binary version of user program\n");
	}
	else if(pid == 0)
	{
	  /* this is the child */
	  execv(fname, argv);
	  printf("if this line is printed then executing user program failed\n");
	}
	else
	{
	  /* this is the parent */
	  wait(&status);
	  printf("executing user program succeed!\n");
	}
}

void execute (char * fname) {
	executeMlton (fname);
	executeProgram (fname);
}

main () {
	char fname[20];
	gets (fname);
	executeMlton (fname);
	executeProgram (fname);
}