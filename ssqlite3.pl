#!/usr/bin/perl
use Modern::Perl;
use IO::All;

system("make");
system("./splitter");
printf( "+++++++++++++++++++++ ^^ cils compilation errors disreguard ^^ +++++++++++++++++++++\n");
system("gcc -ggdb -c th3.c");
system("cd k; gcc -DSQLITE_NO_SYNC -ggdb -c sqlite3.cil.c -o sqlite3_split.o -l dl -l pthread 2>&1 |grep error");
system("cd k; gcc -ggdb ../th3.o sqlite3_split.o -o sqlite3 -l dl -l pthread");
system("cd k; ./sqlite3");
