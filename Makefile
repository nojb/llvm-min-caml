llvm-min-caml:
	ocamlbuild main.native

clean:
	ocamlbuild -clean

.PHONY: llvm-min-caml clean
