(lang dune 3.21)

(using rocq 0.11)

(name coq-hott)

(generate_opam_files true)

(package
 (name coq-hott)
 (source
  (github HoTT/HoTT))
 (homepage "http://homotopytypetheory.org/")
 (license BSD-2-Clause)
 (authors "The HoTT Library Development Team")
 (maintainers
  "Jason Gross <jgross@mit.edu>"
  "Ali Caglayan <alizter@gmail.com>")
 (synopsis "The Homotopy Type Theory library")
 (description
  "\| To use the HoTT library, the following flags must be passed to rocq:
  "\|   -noinit -indices-matter
  "\| To use the HoTT library in a project, add the following to _CoqProject:
  "\|   -arg -noinit
  "\|   -arg -indices-matter
 )
 (depends
  (rocq-core (>= 9.0.0))))
