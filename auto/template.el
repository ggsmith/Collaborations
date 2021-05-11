(TeX-add-style-hook
 "template"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("amsart" "12pt" "leqno")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("xcolor" "svgnames") ("paralist" "alwaysadjust") ("amsrefs" "alphabetic") ("fontenc" "T1") ("hyperref" "colorlinks=true" "linkcolor=DarkBlue" "urlcolor=DarkRed" "citecolor=DarkGreen") ("geometry" "centering" "includeheadfoot" "hmargin=1.0in" "tmargin=1.0in" "bmargin=1in" "headheight=6pt")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "amsart"
    "amsart12"
    "amsmath"
    "amssymb"
    "amsthm"
    "xcolor"
    "tikz"
    "mathtools"
    "paralist"
    "amsrefs"
    "fontenc"
    "mathptmx"
    "microtype"
    "hyperref"
    "caption"
    "subcaption"
    "geometry"
    "listings")
   (TeX-add-symbols
    "PP")
   (LaTeX-add-labels
    "Stanley-Reisner ideal and Alexander duality"
    "the figure 8 and its dual")
   (LaTeX-add-environments
    "example")
   (LaTeX-add-amsthm-newtheorems
    "lemma"
    "theorem"
    "maintheorem"
    "corollary"
    "proposition"
    "definition"
    "remark"
    "examplex"
    "question"))
 :latex)
