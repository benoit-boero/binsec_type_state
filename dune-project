(lang dune 3.17)

(using dune_site 0.1)

(package
 (name type_state)
 (depends
  (ocamlformat
   (and
    :with-dev-setup
    (= 0.26.2)))))
