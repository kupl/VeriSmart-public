#!/usr/bin/env bash

TARGET=main.native
INCLUDE_DIRS=src/frontend,src/pre,src/pre/interval,src/verify,src/vlang,src/util,src/checker,src/exploit

build:
	time ocamlbuild src/$(TARGET) -use-ocamlfind -tag thread -Is $(INCLUDE_DIRS)

clean:
	ocamlbuild -clean

rebuild: clean build

.PHONY: clean build rebuild debug
