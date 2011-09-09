#!/usr/bin/perl
use Modern::Perl;
use IO::All;

system("make");
system("./splitter");
printf( "+++++++++++++++++++++ ^^ cils compilation errors disreguard ^^ +++++++++++++++++++++\n");
system("gcc -ggdb -c th3.c");
system("cd k; gcc -ggdb -c sqlite3.i_split.c -o sqlite3.i_split.o -l dl -l pthread 2>&1 |grep error");
system("cd k; gcc -ggdb ../th3.o sqlite3.i_split.o -o sqlite3 -l dl -l pthread");
