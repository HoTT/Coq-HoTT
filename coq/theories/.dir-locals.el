((coq-mode . ((eval . (let ((default-directory (locate-dominating-file
                                                buffer-file-name ".dir-locals.el")))
                        (make-local-variable 'coq-prog-args)
                        (setq coq-prog-args `("-indices-matter" "-nois" "-coqlib" ,(expand-file-name "..") "-R" ,(expand-file-name ".") "Coq" "-emacs")))))))
