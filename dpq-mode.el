;; This should be loaded with (load "dpq-mode.el") in your
;; .emacs file.
(require 'comint)
(require 'compile)
(set-face-foreground 'font-lock-builtin-face "#2aa198")
(setq-default indent-tabs-mode nil)

(setq dpq-myKeywords
      '(
        ("\\b\\(Simple\\|Parameter\\|Unit\\|Type\\)\\b" . font-lock-builtin-face)
        ("\\b[[:upper:]][[:alnum:]'_]*\\b" . font-lock-type-face)
        
        ("\\b\\(let\\|in\\|do\\|simple\\|forall\\|infixr\\|infixl\\|infix\\|import\\|type\\|gate\\|data\\|class\\|exists\\|instance\\|object\\|case\\|of\\|module\\|where\\|if\\|then\\|else\\)\\b" . font-lock-keyword-face)
        ("\\b\\(box\\|unbox\\|reverse\\|dynlift\\|controlled\\|existsBox\\|withComputed\\)\\b" . font-lock-constant-face)
        ("\\([\\λ=*]\\|:\\|->\\|<-\\|\\.\\|`[[:lower:]][[:alnum:]'_]*`\\|()\\|!\\|&\\||\\|<\\|>\\|[[]\\|[]]\\|{\\|}\\|[$]\\)" . font-lock-constant-face)

        )
      )

;; syntax table
(defvar dpq-syntax-table nil "Syntax table for `dpq-mode'.")
(setq dpq-syntax-table
      (let ((synTable (make-syntax-table)))
	(modify-syntax-entry ?\{ "(}1nb" synTable)
	(modify-syntax-entry ?\} "){4nb" synTable)
	(modify-syntax-entry ?- "_ 123" synTable)
	(modify-syntax-entry ?\n ">" synTable)
	(modify-syntax-entry ?_ "w")
	(modify-syntax-entry ?# "w")
        synTable))


(define-derived-mode dpq-mode fundamental-mode 
  "dpq-mode is a major mode for editing Dependent-Proto-Quipper."
  :syntax-table dpq-syntax-table
  (setq font-lock-defaults '(dpq-myKeywords))
  (setq mode-name "DPQ")
  (set (make-local-variable 'comment-start) "-- ")
  (define-key dpq-mode-map (kbd "C-c C-l") 'dpq-repl-load)
)


;; Adapted from Iowa trellys' emacs mode, fixed a problem in dpq-repl-send-cmd by
;; trial and error. 

(defconst dpq-repl-error-regexp-alist
    `(("^\\(.+?\\):\\([0-9]+\\):\\(\\([0-9]+\\):\\)?\\( \\|\n *\\)\\(error\\)?"
     1 2 4 ,@(if (fboundp 'compilation-fake-loc)
                 '((6) nil (5 '(face nil font-lock-multiline t)))))))

(setq auto-mode-alist (cons '("\\.dpq\\'" . dpq-mode)
			    auto-mode-alist))

(defun dpq-repl-load ()
        "Load the file in the current buffer."
        (interactive)
        (let ((filename (buffer-file-name)))
          (when buffer-file-name (save-buffer))
          (dpq-repl-send-cmd ":l" filename)))

;; dpq-repl-send-cmd currently assume arg is a one element list.
(defun dpq-repl-send-cmd (cmd &optional arg)
  (interactive)
  (dpq-run-repl)
  (let ((newcmd (concat cmd " " "\"" arg "\"" "\n")))
    (comint-send-string inferior-dpq-buffer newcmd))
  )

(defvar inferior-dpq-buffer nil)

;; run dpqi 
(defcustom dpq-repl-command "dpqi" "")

(defun dpq-run-repl (&optional switch-p)
  (if (not (comint-check-proc "*dpq*"))
      (save-excursion (let ((cmdlist nil))
                        (set-buffer (apply 'make-comint "dpq"
                                           dpq-repl-command
                                           nil nil))
                        (dpq-repl-mode))))
  (setq inferior-dpq-buffer "*dpq*")
  (unless (get-buffer-window inferior-dpq-buffer 0)
      (pop-to-buffer inferior-dpq-buffer nil t)
    )


  )

(define-derived-mode dpq-repl-mode comint-mode "dpq"
        "Mode for interacting with dpq interactive process"
        (set (make-local-variable 'comint-prompt-regexp)
                         "^> ")
        (set (make-local-variable 'compilation-error-regexp-alist)
             dpq-repl-error-regexp-alist)
        (set (make-local-variable 'compilation-first-column) 0) 
        (compilation-shell-minor-mode 1))

(provide 'dpq-mode)
