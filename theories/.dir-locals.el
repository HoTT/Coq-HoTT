((coq-mode . ((eval . (let ((default-directory (locate-dominating-file
						buffer-file-name ".dir-locals.el")))
			(setq coq-prog-name (expand-file-name "../hoqtop")))))))
