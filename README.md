TLC4B
=====

This project contains a translator from B to TLA+ with the purpose of applying the
TLC model checker on B models within the ProB validation tool.

TLC is an efficient model checker for TLA+ specifications, which can check LTL properties with fairness. It is particularly good for lower level specifications, where it can be substantially faster than ProB's own model checker

The following article describes the translation:
Dominik Hansen and Michael Leuschel.
Translating B to TLA+ for validation with TLC.
Sci. Comput. Program. 131, pages 109-125. 2016.
[Link](https://doi.org/10.1016/j.scico.2016.04.014)

More details about using TLC4B can be found on the [ProB web pages](https://prob.hhu.de/w/index.php?title=TLC).

[![GitLab CI](https://gitlab.cs.uni-duesseldorf.de/general/stups/tlc4b/badges/develop/pipeline.svg)](https://gitlab.cs.uni-duesseldorf.de/general/stups/tlc4b/pipelines)
