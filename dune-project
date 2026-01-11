(lang dune 3.13)

(using coq 0.8)

(name coq-hott)

(generate_opam_files true)

(source
 (github HoTT/HoTT))

(homepage "http://homotopytypetheory.org/")

(license BSD-2-Clause)

(authors "The HoTT Library Development Team")

(maintainers
 "Jason Gross <jgross@mit.edu>"
 "Ali Caglayan <alizter@gmail.com>")

(package
 (name coq-hott)
 (synopsis "The Homotopy Type Theory library")
 (description
  "To use the HoTT library, the following flags must be passed to rocq:\n  -noinit -indices-matter\nTo use the HoTT library in a project, add the following to _CoqProject:\n  -arg -noinit\n  -arg -indices-matter\n")
 (depends
  (rocq (>= 9.0.0))))
