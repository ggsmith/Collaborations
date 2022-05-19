(TeX-add-style-hook
 "herseySmithZotine"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("amsart" "12pt" "leqno")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("xcolor" "svgnames") ("amsrefs" "shortalphabetic") ("fontenc" "T1") ("beramono" "scaled=0.75") ("hyperref" "colorlinks=true" "linkcolor=DarkBlue" "urlcolor=DarkRed" "citecolor=DarkGreen") ("geometry" "centering" "includeheadfoot" "hmargin=0.95in" "tmargin=0.8in" "bmargin=0.8in" "headheight=6pt")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
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
    "amsrefs"
    "fontenc"
    "mathptmx"
    "microtype"
    "beramono"
    "hyperref"
    "caption"
    "subcaption"
    "geometry"
    "listings"
    "stix")
   (TeX-add-symbols
    "colequal"
    "PP")
   (LaTeX-add-labels
    "bowtie"
    "Gamma")
   (LaTeX-add-amsthm-newtheorems
    "lemma"
    "theorem"
    "maintheorem"
    "corollary"
    "proposition"
    "definition"
    "remark"
    "example"
    "question"))
 :latex)

