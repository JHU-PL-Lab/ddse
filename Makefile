.PHONY: all clean repl test benchmark

all:
	dune build
	dune build src/toploop-main/ddpa_toploop.exe
	dune build src/odefa-natural-translator-main/translator.exe
	dune build src/test-generation-main/test_generator.exe
	rm -f ddpa_toploop
	rm -f translator
	rm -f test_generator
	ln -s _build/default/src/toploop-main/ddpa_toploop.exe ddpa_toploop
	ln -s _build/default/src/test-generation-main/test_generator.exe test_generator
	ln -s _build/default/src/odefa-natural-translator-main/translator.exe translator

sandbox:
	dune build test/sandbox.exe

repl:
	dune utop src -- -require pdr-programming

test:
	dune runtest -f

clean:
	dune clean
	rm -f ddpa_toploop
	rm -f translator

benchmark:
	ocaml bench/benchmark.ml