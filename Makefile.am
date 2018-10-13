EXTRA_DIST = m4

ACLOCAL_AMFLAGS = -I m4

SUBDIRS = src

sub_targets = run prog view

$(sub_targets):
	$(MAKE) $(AM_MAKEFLAGS) -C src $@

.PHONY: $(sub_targets)

DISTCLEANFILES = \
$(builddir)/test_out.* \
$(builddir)/test_in.*
