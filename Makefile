# -*- Makefile -*-

# --------------------------------------------------------------------
NAME     := SsrECGLV
INCFLAGS :=
INCFLAGS += -R mpoly/3rdparty $(NAME) -R mpoly/finmap $(NAME) -R mpoly/src $(NAME)
INCFLAGS += -R 3rdparty $(NAME) -R common $(NAME) -R src $(NAME)
SUBDIRS  := mpoly
COQFILES := \
  3rdparty/fraction.v \
  3rdparty/polyorder.v \
  common/ssrring.v \
  common/fracfield.v \
  common/polyall.v \
  common/polydec.v \
  common/polyfrac.v \
  common/xmatrix.v \
  common/xseq.v \
  src/ec.v \
  src/ecpoly.v \
  src/ecpolyfrac.v \
  src/ecorder.v \
  src/eceval.v \
  src/ecdiv.v \
  src/ecrr.v \
  src/ecdivlr.v \
  src/ecgroup.v \
  src/ecprojective.v \
  src/endomorphism.v \
  src/multiexponentiation.v \
  src/glv.v

include Makefile.common

# --------------------------------------------------------------------
.PHONY: install

install:
	$(MAKE) -f Makefile.coq install

# --------------------------------------------------------------------
this-clean::
	rm -f *.glob *.d *.vo

this-distclean::
	rm -f $(shell find . -name '*~')
