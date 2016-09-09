platform ?= $(shell node -p 'process.platform')

.PHONY: install
install:
	ln -fs ../vendor-darwin/share ./vendor-linux/share
	cp -r vendor-$(platform)/lib/* _build/ocamlfind/lib
	cp -RL vendor-$(platform)/share/* _build/ocamlfind/share
