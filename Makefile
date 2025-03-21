DEST_PATH ?= $(HOME)/.local
BIN ?= main
EVE_PATH = $(DEST_PATH)/eve
STD_PATH ?= $(EVE_PATH)/std
BIN_PATH = $(EVE_PATH)/bin

default: debug

install: compile-debug install-std
	@echo "==> Installing."
	mkdir -p $(BIN_PATH)
	cp ./$(BIN) $(BIN_PATH)

install-std:
	@echo "==> Installing standard library."
	mkdir -p $(STD_PATH)
	cp -r ./std/* $(STD_PATH)

gen-constants: constants.in
	@cat constants.in > constants.rs
	@echo -n '$(STD_PATH)' >> constants.rs
	@echo "\");" >> constants.rs
	@mv constants.rs ./src/constants.rs

compile-debug: gen-constants
	cargo build && cp ./target/debug/main ./$(BIN)

debug:
	@STD_PATH=$(PWD)/std/ make debug-internal

debug-internal: gen-constants compile-debug

.PHONY: default install install-std gen-constants compile-debug debug debug-internal clean

clean:
	-rm ./$(BIN)
	-rm ./src/constants.rs
