# Lwc: Light weight concurrency in Ocaml

#LIB=/usr/local/godi/lib/ocaml/pkg-lib
#LIB2=/usr/local/godi/lib/ocaml/std-lib
LIB=/usr/lib/ocaml/

# godi new builds lwt-unix.cma instead of lwt_unix.cma...

OCAMLC=ocamlc
OCAMLOPT=ocamlopt

SIEVE=sieve_tramp sieve_cont sieve_callcc sieve_dlcont sieve_sys sieve_vm sieve_promise sieve_lwt sieve_mcon
SIEVE_OPT=sieve_tramp.opt sieve_cont.opt sieve_sys.opt sieve_promise.opt sieve_lwt.opt 

KPN=kpn_tramp kpn_cont kpn_callcc kpn_dlcont kpn_sys kpn_vm kpn_promise kpn_mcon
KPN_OPT=kpn_tramp.opt kpn_cont.opt kpn_sys.opt kpn_promise.opt 

SORTER=sorter_tramp sorter_cont sorter_callcc sorter_dlcont sorter_sys sorter_vm sorter_promise sorter_mcon
SORTER_OPT=sorter_tramp.opt sorter_cont.opt sorter_sys.opt sorter_promise.opt 

# make all the executables
# need to clean up between each example application
all:
	make kpn.bc
	make kpn.opt
	make clean
	make sorter.bc
	make sorter.opt
	make clean
	make sieve.bc
	make sieve.opt
	make clean

sieve.bc: $(SIEVE)
sieve.opt: $(SIEVE_OPT)
kpn.bc: $(KPN)
kpn.opt: $(KPN_OPT)
sorter.bc: $(SORTER)
sorter.opt: $(SORTER_OPT)


clean:
	rm -f a.out *.o *.opt *.cmi *.cmo *.cmi *.cmx *~
	rm -f *.htoc *.aux *.haux *.log *.blg *.dvi *.ps
	rm -f lwc.ml lwc.mli

# also remove executables
doclean:: clean
	rm -f $(SIEVE) $(SIEVE_OPT) $(KPN) $(KPN_OPT) $(SORTER) $(SORTER_OPT)

purge: doclean
	rm -f *.html *.png


%.cmi : %.mli
	$(OCAMLC) -c $<

%.cmo : %.ml
	$(OCAMLC) -c $<

%.cmx : %.ml
	ocamlopt -c $<


# objects for sieve
S_CMO=main.cmo lwc.cmo
S_CMX=main.cmx lwc.cmx
S_MCON_CMO=unix.cma nums.cma main.cmo mconbase.cmo sugarcube.cmo mvars.cmo

# objects for KPN
K_CMO=unix.cma nums.cma kmain.cmo lwc.cmo
K_CMX=unix.cmxa nums.cmxa kmain.cmx lwc.cmx
K_MCON_CMO=unix.cma nums.cma kmain.cmo mconbase.cmo sugarcube.cmo mvars.cmo

# objects for KPN w/o unix (is present before on command line)
KNU_CMO=nums.cma kmain.cmo lwc.cmo
KNU_CMX=nums.cmxa kmain.cmx lwc.cmx

# preempt

sys:
	rm -f lwc.*
	ln -s lwc_preempt.ml lwc.ml
	ln -s lwc_direct.mli lwc.mli
	ocamlc -c lwc.mli
	ocamlc -thread -c lwc.ml
	ocamlopt -thread -c lwc.ml

vm:
	rm -f lwc.*
	ln -s lwc_preempt.ml lwc.ml
	ln -s lwc_direct.mli lwc.mli
	ocamlc -c lwc.mli
	ocamlc -vmthread -c lwc.ml

sieve_sys: sieve_direct.ml main.cmo sys
	ocamlc -o $@ -thread unix.cma threads.cma $(S_CMO) $<

sieve_sys.opt: sieve_direct.ml main.cmx sys
	ocamlopt -o $@ -thread unix.cmxa threads.cmxa $(S_CMX) $<

sieve_vm: sieve_direct.ml main.cmo vm
	ocamlc -o $@ -vmthread threads.cma unix.cma $(S_CMO) $<

kpn_sys: kpn_direct.ml kmain.cmo sys
	ocamlc -o $@ -thread unix.cma threads.cma $(KNU_CMO) $<

kpn_sys.opt: kpn_direct.ml kmain.cmx sys
	ocamlopt -o $@ -thread unix.cmxa threads.cmxa $(KNU_CMX) $<

kpn_vm: kpn_direct.ml kmain.cmo vm
	ocamlc -o $@ -vmthread threads.cma unix.cma $(KNU_CMO) $<


sorter_sys: sorter_direct.ml main.cmo sys
	ocamlc -o $@ -thread unix.cma threads.cma $(S_CMO) $<

sorter_sys.opt: sorter_direct.ml main.cmx sys
	ocamlopt -o $@ -thread unix.cmxa threads.cmxa $(S_CMX) $<

sorter_vm: sorter_direct.ml main.cmo vm
	ocamlc -o $@ -vmthread threads.cma unix.cma $(S_CMO) $<


# callcc

LOCALDIR=/usr/lib/ocaml

callcc:
	rm -f lwc.*
	ln -s lwc_callcc.ml lwc.ml
	ln -s lwc_direct.mli lwc.mli
	ocamlc -c lwc.mli
	ocamlc -c -I $(LOCALDIR) lwc.ml
	ocamlopt -c -I $(LOCALDIR) lwc.ml

sieve_callcc: sieve_direct.ml main.cmo callcc
	ocamlc -o $@ -I $(LOCALDIR) callcc.cma unix.cma $(S_CMO) $<

kpn_callcc: kpn_direct.ml callcc kmain.cmo
	ocamlc -o $@ -I $(LOCALDIR) callcc.cma $(K_CMO) $<

sorter_callcc: sorter_direct.ml callcc kmain.cmo
	ocamlc -o $@ -I $(LOCALDIR) unix.cma callcc.cma $(S_CMO) $<


# dlcont

dlcont:
	rm -f lwc.*
	ln -s lwc_dlcont.ml lwc.ml
	ln -s lwc_direct.mli lwc.mli
	ocamlc -c lwc.mli
	ocamlc -c -I $(LOCALDIR) lwc.ml
	ocamlopt -c -I $(LOCALDIR) lwc.ml

sieve_dlcont: sieve_direct.ml main.cmo dlcont
	 ocamlc -o $@ -I $(LOCALDIR) delimcc.cma unix.cma $(S_CMO) $<

kpn_dlcont: kpn_direct.ml dlcont kmain.cmo
	ocamlc -o $@ -I $(LOCALDIR) delimcc.cma $(K_CMO) $<

sorter_dlcont: sorter_direct.ml dlcont
	ocamlc -o $@ unix.cma -I $(LOCALDIR) delimcc.cma $(S_CMO) $<

sieve_dlcont.opt: sieve_direct.ml main.cmx dlcont
	 ocamlopt -o $@ -I $(LOCALDIR) -cclib -L$(LIB2) delimcc.cmxa unix.cmxa $(S_CMX) $<

kpn_dlcont.opt: kpn_direct.ml dlcont kmain.cmx
	 ocamlopt -o $@ -I $(LOCALDIR) -cclib -L$(LIB2) delimcc.cmxa $(K_CMX) $<

sorter_dlcont.opt: sorter_direct.ml dlcont
	 ocamlopt -o $@ unix.cmxa -I $(LOCALDIR) -cclib -L$(LIB2) delimcc.cmxa $(S_CMX) $<

# Lwt

LWTDIR=$(HOME)/.opam/system/lib/lwt

lwt:
	rm -f lwc.*
	ln -s lwc_lwt.ml lwc.ml
	ln -s lwc_lwt.mli lwc.mli
	ocamlc -I $(LWTDIR) -c lwc.mli
	ocamlc -I $(LWTDIR) -c lwc.ml
	ocamlopt -I $(LWTDIR) -c lwc.ml
lwt_mv:
	rm -f lwc.*
	ln -s lwc_lwt_mv.ml lwc.ml
	ln -s lwc_lwt_mv.mli lwc.mli
	ocamlc -I $(LWTDIR) -c lwc.mli
	ocamlc -I $(LWTDIR) -c lwc.ml
	ocamlopt -I $(LWTDIR) -c lwc.ml

sieve_lwt: sieve_indirect.ml main.cmo lwt
	ocamlc -o $@ -I $(LWTDIR) unix.cma lwt.cma lwt-unix.cma  $(S_CMO) $<

sieve_lwt.opt: sieve_indirect.ml main.cmx lwt
	ocamlopt -o $@ -I $(LWTDIR) unix.cmxa lwt.cmxa lwt-unix.cmxa $(S_CMX) $<

kpn_lwt: kpn_indirect.ml kmain.cmo lwt
	ocamlc -o $@ -I $(LWTDIR) unix.cma lwt.cma lwt-unix.cma $(KNU_CMO) $<

kpn_lwt.opt: kpn_indirect.ml kmain.cmx lwt
	ocamlopt -o $@ -I $(LWTDIR) unix.cmxa lwt.cmxa lwt-unix.cmxa $(KNU_CMX) $<

sorter_lwt: sorter_lwt.ml main.cmo lwt
	ocamlc -o $@ -I $(LWTDIR) unix.cma lwt.cma lwt-unix.cma $(S_CMO) $<

sorter_lwt.opt: sorter_lwt.ml main.cmx lwt
	ocamlopt -o $@ -I $(LWTDIR) unix.cmxa lwt.cmxa lwt-unix.cmxa $(S_CMX) $<


# trampoline

tramp:
	rm -f lwc.*
	ln -s lwc_tramp.ml lwc.ml
	ln -s lwc_indirect.mli lwc.mli
	ocamlc -c lwc.mli
	ocamlc -c lwc.ml
	ocamlopt -c lwc.ml

sieve_tramp: sieve_indirect.ml tramp main.cmo
	ocamlc -o $@ unix.cma $(S_CMO) $<

sieve_tramp.opt: sieve_indirect.ml tramp main.cmx
	ocamlopt -o $@ unix.cmxa $(S_CMX) $<

kpn_tramp: kpn_indirect.ml tramp kmain.cmo
	ocamlc -o $@ $(K_CMO) $<

kpn_tramp.opt: kpn_indirect.ml kmain.cmx tramp
	ocamlopt -o $@ $(K_CMX) $<

sorter_tramp: sorter_indirect.ml main.cmo tramp
	ocamlc -o $@ unix.cma $(S_CMO) $<

sorter_tramp.opt: sorter_indirect.ml tramp main.cmx
	ocamlopt -o $@ unix.cmxa $(S_CMX) $<


# continuation monad

cont:
	rm -f lwc.*
	ln -s lwc_cont.ml lwc.ml
	ln -s lwc_monad.mli lwc.mli
	ocamlc -c lwc.mli
	ocamlc -c lwc.ml
	ocamlopt -c lwc.ml

mcon: 
	ocamlc -c mconbase.ml
	ocamlc -c sugarcube.ml mconbase.cmo
	ocamlc -c mvars.ml mconbase.cmo

sieve_cont: sieve_indirect.ml cont main.cmo
	ocamlc -o $@ unix.cma $(S_CMO) $<

sieve_mcon: sieve_mcon.ml mcon main.cmo
	ocamlc -o $@ $(S_MCON_CMO) $<

sieve_cont.opt: sieve_indirect.ml cont main.cmx
	ocamlopt -o $@ unix.cmxa $(S_CMX) $<

kpn_cont: kpn_indirect.ml cont kmain.cmo
	ocamlc -o $@ $(K_CMO) $<

kpn_mcon: kpn_mcon.ml mcon kmain.cmo
	ocamlc -o $@ $(K_MCON_CMO) $<

kpn_cont.opt: kpn_indirect.ml kmain.cmx cont
	ocamlopt -o $@ $(K_CMX) $<

sorter_cont: sorter_monad.ml main.cmo cont
	ocamlc -o $@ unix.cma $(S_CMO) $<

sorter_mcon: sorter_mcon.ml mcon main.cmo
	ocamlc -o $@ $(S_MCON_CMO) $<

sorter_cont.opt: sorter_monad.ml cont main.cmx
	ocamlopt -o $@ unix.cmxa $(S_CMX) $<

# promise monad

promise:
	rm -f lwc.*
	ln -s lwc_promise.ml lwc.ml
	ln -s lwc_monad.mli lwc.mli
	ocamlc -c lwc.mli
	ocamlc -c lwc.ml
	ocamlopt -c lwc.ml

sieve_promise: sieve_indirect.ml promise main.cmo
	ocamlc -o $@ unix.cma $(S_CMO) $<

sieve_promise.opt: sieve_indirect.ml promise main.cmx
	ocamlopt -o $@ unix.cmxa $(S_CMX) $<

kpn_promise: kpn_indirect.ml promise kmain.cmo
	ocamlc -o $@ $(K_CMO) $<

kpn_promise.opt: kpn_indirect.ml kmain.cmx promise
	ocamlopt -o $@ $(K_CMX) $<

sorter_promise: sorter_monad.ml main.cmo promise
	ocamlc -o $@ unix.cma $(S_CMO) $<

sorter_promise.opt: sorter_monad.ml promise main.cmx
	ocamlopt -o $@ unix.cmxa $(S_CMX) $<


# equeue

EQUEUEDIR=/usr/local/lib/ocaml/3.12.1/equeue

# build equeue with Big_ints: used by kpn
equeue_bi:
	rm -f lwc.*
	sed -e "s/esys : int/esys : Big_int.big_int/" lwc_equeue.ml > lwc.ml
	sed -e "s/'a mvar -> 'a /Big_int.big_int mvar -> Big_int.big_int /" -e "s/'a mvar -> ('a /Big_int.big_int mvar -> (Big_int.big_int /" -e "s/'a fifo -> 'a/Big_int.big_int fifo -> Big_int.big_int/" -e "s/'a fifo -> ('a/Big_int.big_int fifo -> (Big_int.big_int/" lwc_indirect.mli > lwc_equeue.mli
	ln -s lwc_equeue.mli lwc.mli
	ocamlc -c -I $(EQUEUEDIR) lwc.mli
	ocamlc -I $(EQUEUEDIR) -c lwc.ml
	ocamlopt -I $(EQUEUEDIR) -c lwc.ml

# build equeue with ints
equeue:
	rm -f lwc.*
	cp lwc_equeue.ml lwc.ml
	sed -e "s/'a mvar -> 'a /int mvar -> int /" -e "s/'a mvar -> ('a /int mvar -> (int /" -e "s/'a fifo -> 'a/int fifo -> int/" -e "s/'a fifo -> ('a/int fifo -> (int/" lwc_indirect.mli > lwc_equeue.mli
	ln -s lwc_equeue.mli lwc.mli
	ocamlc -c  -I $(EQUEUEDIR) lwc.mli
	ocamlc -I $(EQUEUEDIR) -c lwc.ml
	ocamlopt -I $(EQUEUEDIR) -c lwc.ml

sieve_equeue: sieve_indirect.ml main.cmo equeue
	ocamlc -o $@ -I $(EQUEUEDIR) equeue.cma unix.cma $(S_CMO) $<

sieve_equeue.opt: sieve_indirect.ml main.cmx equeue
	ocamlopt -o $@ -I $(EQUEUEDIR) equeue.cmxa unix.cmxa $(S_CMX) $<

kpn_equeue: kpn_indirect.ml kmain.cmo equeue_bi
	ocamlc -o $@ -I $(EQUEUEDIR) equeue.cma $(K_CMO) $<

kpn_equeue.opt: kpn_indirect.ml kmain.cmx equeue_bi
	ocamlopt -o $@ -I $(EQUEUEDIR) equeue.cmxa $(K_CMX) $<

sorter_equeue: sorter_indirect.ml main.cmo equeue
	ocamlc -o $@ -I $(EQUEUEDIR) equeue.cma unix.cma $(S_CMO) $<

sorter_equeue.opt: sorter_indirect.ml main.cmx equeue
	ocamlopt -o $@ -I $(EQUEUEDIR) equeue.cmxa unix.cmxa $(S_CMX) $<

