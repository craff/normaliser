# You should not need to modify anything in this file. If you need to
# do so, report a bug so that I can modify my installation procedure.

CAMLLEX=ocamllex
CAMLYACC=ocamlyacc -v -q

CAMLC = ocamlc
CAMLO = ocamlopt
ZFLAGS =

CAMLDEP = ocamldep

# you should know what you are doing if you modify anything beyond this line

TARGET = lambda
#TARGET = lambdaopt

FILES = format.cmo bindlib.cmo lambda.cmo typing.cmo \
        parser_tool.cmo action.cmo parser.cmo lexer.cmo main.cmo
FILESO = format.cmx bindlib.cmx lambda.cmx typing.cmx \
         parser_tool.cmx action.cmx parser.cmx lexer.cmx main.cmx

lambda : $(FILES) depend
	$(CAMLC) $(ZFLAGS) -o $@ $(FILES)

lambdaopt : $(FILESO) depend
	$(CAMLO) $(ZFLAGS) -o $@ $(FILESO)

clean:
	- rm -f *.cmi *.cmo *.cmx *.o \
	        parser.ml parser.mli lexer.ml lambda lambdaopt

.SUFFIXES :
.SUFFIXES : .mli .ml .cmi .cmx .cmo .mly .mll

.mli.cmi:
	$(CAMLC) $(ZFLAGS) -c $<

.ml.cmo:
	$(CAMLC) $(ZFLAGS) -c $<

.ml.cmx:
	$(CAMLO) $(ZFLAGS) -c $<

lexer.ml: lexer.mll
	$(CAMLLEX) lexer.mll

parser.mli: parser.mly preparser.mli
	$(CAMLYACC) parser.mly; \
        mv parser.mli parser.tmp; \
        cat preparser.mli > parser.mli; \
        cat parser.tmp >> parser.mli; \
        mv parser.ml parser.tmp; \
        cat preparser.mli > parser.ml; \
        cat parser.tmp >> parser.ml; \
        rm parser.tmp
parser.ml : parser.mli

depend: parser.ml lexer.ml
	- rm depend; \
	$(CAMLDEP) *.ml *.mli *.mlp *.mlip > depend

install: $(TARGET)
	cp $(TARGET) $(BINDIR)

#dependencies
include depend
