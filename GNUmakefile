AGDA_BIN    ?= agda
RTS_OPTIONS ?= +RTS -M8G -H3.5G -A128M -s -RTS
AGDA_EXEC   = $(AGDA_BIN) $(RTS_OPTIONS)

everything: Everything.agda
	$(AGDA_EXEC) -i. -isrc Everything.agda --profile=internal

.PHONY: listings
listings: Everything.agda
	$(AGDA_EXEC) -i. -isrc --html README.agda -v0

# setup: Everything.agda
# 
# .PHONY: Everything.agda
# Everything.agda:
# # The command `cabal build` is needed by cabal-install 3.0.0.0 and the
# # command `cabal install` is needed by cabal-install <= 2.4.*. I did
# # not found any problem running both commands with different versions
# # of cabal-install. See Issue #1001.
# 	cabal run GenerateEverything

clean :
	rm -rf _build