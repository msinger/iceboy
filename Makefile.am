EXTRA_DIST = m4

ACLOCAL_AMFLAGS = -I m4

SUBDIRS = src tests sim

sub_targets = run prog view

$(sub_targets):
	$(MAKE) $(AM_MAKEFLAGS) -C src $@

.PHONY: $(sub_targets)

hwtests:
	$(MAKE) $(AM_MAKEFLAGS) -C tests $@

.PHONY: hwtests

DISTCLEANFILES = \
$(builddir)/test_out.* \
$(builddir)/test_in.*

DISTCHECK_CONFIGURE_FLAGS = --without-bootrom
