((coq-mode . ((eval . (let ((default-directory (locate-dominating-file
						buffer-file-name ".dir-locals.el")))
			(make-local-variable 'coq-prog-name)
			(setq coq-prog-name (expand-file-name "../hoqtop")))))))
