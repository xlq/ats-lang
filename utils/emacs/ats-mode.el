;;; ats-mode.el --- Major mode to edit ATS source code

;; Copyright (C) 2007  Stefan Monnier
;; updated and modified by Matthew Danish <md@bu.edu> 2008

;; Author: Stefan Monnier <monnier@iro.umontreal.ca>
;; Keywords: 

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; Todo:
;; - font-lock
;; - imenu
;; - outline
;; - indentation

;;; Code:

(require 'cl)
(require 'compile)

(when (not (boundp 'xemacsp))
  (setq xemacsp (boundp 'xemacs-logo)))

(defvar ats-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; (*..*) for nested comments.
    (modify-syntax-entry ?\( "()1n" st)
    (modify-syntax-entry ?\) ")(4n" st)
    (modify-syntax-entry ?*  ". 23" st)
    ;; Not sure how to do // for single-line comments.
    ;; The current setting means that (/ and /* start a comment as well :-(
    (modify-syntax-entry ?/  ". 12b" st)
    (modify-syntax-entry ?\n ">  b" st)
    ;; Strings.
    (modify-syntax-entry ?\" "\"" st)
    ;; Same problem as in Ada: ' starts a char-literal but can appear within
    ;; an identifier.  So we can either default it to "string" syntax and
    ;; let font-lock-syntactic-keywords correct its uses in symbols, or
    ;; the reverse.  We chose the reverse, which fails more gracefully.
    ;; Oh, and ' is also overloaded for '( '{ and '[  :-(
    (modify-syntax-entry ?\' "_ p" st)
    ;; 
    (modify-syntax-entry ?\{ "()" st)
    (modify-syntax-entry ?\} ")(" st)
    (modify-syntax-entry ?\[ "()" st)
    (modify-syntax-entry ?\] ")(" st)
    ;; Skip over @/# when going backward-sexp over @[...], #[...],
    ;; #ident and $ident.
    (modify-syntax-entry ?\@ ". p" st)
    (modify-syntax-entry ?\# ". p" st)
    (modify-syntax-entry ?\$ ". p" st)
    ;; Same thing for macro&meta programming.
    (modify-syntax-entry ?\` ". p" st)
    (modify-syntax-entry ?\, ". p" st)
    ;; Just a guess for now.
    (modify-syntax-entry ?\\ "\\" st)
    ;; Handle trailing +/-/* in keywords.
    ;; (modify-syntax-entry ?+ "_" st)
    ;; (modify-syntax-entry ?- "_" st)
    ;; (modify-syntax-entry ?* "_" st)
    ;; Symbolic identifiers are kind of like in SML, which is poorly
    ;; supported by Emacs.  Worse: there are 2 kinds, one where "!$#?" are
    ;; allowed and one where "<>" are allowed instead.  Hongwei, what's that
    ;; all about?
    (modify-syntax-entry ?% "." st)
    (modify-syntax-entry ?& "." st)
    (modify-syntax-entry ?+ "." st)
    (modify-syntax-entry ?- "." st)
    (modify-syntax-entry ?. "." st)
    ;; (modify-syntax-entry ?/ "." st)  ; Already covered above for comments.
    (modify-syntax-entry ?: "." st)
    (modify-syntax-entry ?= "." st)
    ;; (modify-syntax-entry ?@ "." st)  ; Already defined above.
    (modify-syntax-entry ?~ "." st)
    ;; (modify-syntax-entry ?` "." st)  ; Already defined above.
    (modify-syntax-entry ?^ "." st)
    (modify-syntax-entry ?| "." st)
    ;; (modify-syntax-entry ?* "." st)  ; Already covered above for comments.
    (modify-syntax-entry ?< "." st)
    (modify-syntax-entry ?> "." st)
    (modify-syntax-entry ?! "." st)
    ;; (modify-syntax-entry ?$ "." st)  ; Already defined above.
    ;; (modify-syntax-entry ?# "." st)  ; Already defined above.
    (modify-syntax-entry ?? "." st)
    ;; Real punctuation?
    (modify-syntax-entry ?:  "." st)
    (modify-syntax-entry ?\; "." st)
    st))
    
;; Font-lock.

(defvar ats-font-lock-keywords
  '(("\\<absprop\\>" (0 'font-lock-keyword-face))
    ("\\<abstype\\>" (0 'font-lock-keyword-face))
    ("\\<abst@type\\>" (0 'font-lock-keyword-face)) 
    ("\\<absview\\>" (0 'font-lock-keyword-face))
    ("\\<absviewtype\\>" (0 'font-lock-keyword-face))
    ("\\<absviewt@ype\\>" (0 'font-lock-keyword-face))
    ("\\<and\\>" (0 'font-lock-keyword-face))
    ("\\<as\\>" (0 'font-lock-keyword-face))
    ("\\<assume\\>" (0 'font-lock-keyword-face))
    ("\\<begin\\>" (0 'font-lock-keyword-face))
    ("\\<break\\>" (0 'font-lock-keyword-face))
    ("\\<case\\(+\\|*\\)?\\>" (0 'font-lock-keyword-face))
    ("\\<class\\>" (0 'font-lock-keyword-face))
    ("\\<continue\\>" (0 'font-lock-keyword-face))
    ("\\<datasort\\>" (0 'font-lock-keyword-face))
    ("\\<dataprop\\>" (0 'font-lock-keyword-face))
    ("\\<datatype\\>" (0 'font-lock-keyword-face))
    ("\\<dataview\\>" (0 'font-lock-keyword-face))
    ("\\<dataviewtype\\>" (0 'font-lock-keyword-face))
    ("\\<dyn\\>" (0 'font-lock-keyword-face))
    ("\\<dynload\\>" (0 'font-lock-keyword-face))
    ("\\<else\\>" (0 'font-lock-keyword-face))
    ("\\<end\\>" (0 'font-lock-keyword-face))
    ("\\<exception\\>" (0 'font-lock-keyword-face))
    ("\\<extern\\>" (0 'font-lock-keyword-face))
    ("\\<fix\\>" (0 'font-lock-keyword-face))
    ("\\<fn\\>" (0 'font-lock-keyword-face))
    ("\\<for\\>" (0 'font-lock-keyword-face))
    ("\\<fun\\>" (0 'font-lock-keyword-face))
    ("\\<if\\>" (0 'font-lock-keyword-face))
    ("\\<implement\\>" (0 'font-lock-keyword-face))
    ("\\<in\\>" (0 'font-lock-keyword-face))
    ("\\<infix\\>" (0 'font-lock-keyword-face))
    ("\\<infixl\\>" (0 'font-lock-keyword-face))
    ("\\<infixr\\>" (0 'font-lock-keyword-face))
    ("\\<lam\\>" (0 'font-lock-keyword-face))
    ("\\<let\\>" (0 'font-lock-keyword-face))
    ("\\<llam\\>" (0 'font-lock-keyword-face))
    ("\\<local\\>" (0 'font-lock-keyword-face))
    ("\\<macdef\\>" (0 'font-lock-keyword-face))
    ("\\<macrodef\\>" (0 'font-lock-keyword-face))
    ("\\<method\\>" (0 'font-lock-keyword-face))
    ("\\<modprop\\>" (0 'font-lock-keyword-face))
    ("\\<modtype\\>" (0 'font-lock-keyword-face))
    ("\\<module\\>" (0 'font-lock-keyword-face))
    ("\\<nonfix\\>" (0 'font-lock-keyword-face))
    ("\\<overload\\>" (0 'font-lock-keyword-face))
    ("\\<par\\>" (0 'font-lock-keyword-face))
    ("\\<postfix\\>" (0 'font-lock-keyword-face))
    ("\\<praxi\\>" (0 'font-lock-keyword-face))
    ("\\<prefix\\>" (0 'font-lock-keyword-face))
    ("\\<prfn\\>" (0 'font-lock-keyword-face))
    ("\\<prfun\\>" (0 'font-lock-keyword-face))
    ("\\<prval\\>" (0 'font-lock-keyword-face))
    ("\\<object\\>" (0 'font-lock-keyword-face))
    ("\\<of\\>" (0 'font-lock-keyword-face))
    ("\\<op\\>" (0 'font-lock-keyword-face))
    ("\\<propdef\\>" (0 'font-lock-keyword-face))
    ("\\<rec\\>" (0 'font-lock-keyword-face))
    ("\\<sif\\>" (0 'font-lock-keyword-face))
    ("\\<sortdef\\>" (0 'font-lock-keyword-face))
    ("\\<sta\\>" (0 'font-lock-keyword-face))
    ("\\<stadef\\>" (0 'font-lock-keyword-face))
    ("\\<staif\\>" (0 'font-lock-keyword-face))
    ("\\<staload\\>" (0 'font-lock-keyword-face))
    ("\\<stavar\\>" (0 'font-lock-keyword-face))
    ("\\<struct\\>" (0 'font-lock-keyword-face))
    ("\\<symelim\\>" (0 'font-lock-keyword-face))
    ("\\<symintr\\>" (0 'font-lock-keyword-face))
    ("\\<then\\>" (0 'font-lock-keyword-face))
    ("\\<try\\>" (0 'font-lock-keyword-face))
    ("\\<typedef\\>" (0 'font-lock-keyword-face))
    ("\\<union\\>" (0 'font-lock-keyword-face))
    ("\\<val\\>" (0 'font-lock-keyword-face))
    ("\\<var\\>" (0 'font-lock-keyword-face))
    ("\\<viewdef\\>" (0 'font-lock-keyword-face))
    ("\\<viewtypedef\\>" (0 'font-lock-keyword-face))
    ("\\<when\\>" (0 'font-lock-keyword-face))
    ("\\<where\\>" (0 'font-lock-keyword-face))
    ("\\<while\\>" (0 'font-lock-keyword-face))
    ("\\<with\\>" (0 'font-lock-keyword-face))
    ("\\<withprop\\>" (0 'font-lock-keyword-face))
    ("\\<withtype\\>" (0 'font-lock-keyword-face))
    ("\\<withview\\>" (0 'font-lock-keyword-face))
    ("\\<withviewtype\\>" (0 'font-lock-keyword-face))

    (":" (0 'font-lock-type-face))

    ("{" (0 'font-lock-type-face))
    ("}" (0 'font-lock-type-face))
    ("\\[" (0 'font-lock-type-face))
    ("\\]" (0 'font-lock-type-face))

    ;; ("{[^|]*|[^}]*}" (0 'font-lock-type-face))
    ))

(defvar ats-font-lock-syntactic-keywords
  '(("(\\(/\\)" (1 ". 1b"))             ; (/ does not start a comment.
    ("/\\(*\\)" (1 ". 3"))              ; /* does not start a comment.
    ("\\(/\\)///" (0 "< nb"))           ; Start a comment with no end.
    ;; Recognize char-literals.
    ("[^[:alnum:]]\\('\\)\\(?:.\\|\\\\.[[:xdigit:]]*\\)\\('\\)"
     (1 "\"'") (2 "\"'"))
    ))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.\\(d\\|c\\|s\\)ats\\'" . ats-mode))

;;;###autoload
(define-derived-mode ats-mode fundamental-mode "ATS"
  "Major mode to edit ATS source code."
  (set (make-local-variable 'font-lock-defaults)
       '(ats-font-lock-keywords nil nil ((?_ . "w")) nil
         (font-lock-syntactic-keywords . ats-font-lock-syntactic-keywords)))
  (set (make-local-variable 'comment-start) "(*")
  (set (make-local-variable 'comment-continue)  " *")
  (set (make-local-variable 'comment-end) "*)")
  (setq indent-line-function 'tab-to-tab-stop)
  (setq tab-stop-list (loop for x from 2 upto 120 by 2 collect x))
  (setq indent-tabs-mode nil)
  (local-set-key (kbd "RET") 'newline-and-indent-relative)
  (unless (local-variable-p 'compile-command)
    (set (make-local-variable 'compile-command)
         (let ((file buffer-file-name))
           (format "atscc -tc %s" file))))
  (local-set-key (kbd "C-c C-c") 'compile)
  (cond 
   ;; Emacs 21
   ((and (< emacs-major-version 22)
         (not xemacsp)) 
    (pushnew '("\\(syntax error: \\)?\\([^\n:]*\\): \\[?[0-9]*(line=\\([0-9]*\\), offs=\\([0-9]*\\))\\]?" 2 3 4)
             compilation-error-regexp-alist))
   ;; Emacs 22+ has an improved compilation mode
   ((and (>= emacs-major-version 22)
         (not xemacsp))
    (pushnew '(ats "\\(syntax error: \\)?\\([^\n:]*\\): \\[?[0-9]*(line=\\([0-9]*\\), offs=\\([0-9]*\\))\\]?\\(?: -- [0-9]*(line=\\([0-9]*\\), offs=\\([0-9]*\\))\\)?" 2 (3 . 5) (4 . 6))
             compilation-error-regexp-alist-alist)
    (pushnew 'ats compilation-error-regexp-alist))
   ;; XEmacs has something different, to be contrary
   (xemacsp
    (pushnew '(ats ("\\(syntax error: \\)?\\([^\n:]*\\): \\[?[0-9]*(line=\\([0-9]*\\), offs=\\([0-9]*\\))\\]?" 2 3 4))
             compilation-error-regexp-alist-alist)
    (unless (eql 'all compilation-error-regexp-systems-list)
      (pushnew 'ats compilation-error-regexp-systems-list))
    (compilation-build-compilation-error-regexp-alist)
    (message "WARNING! XEMACS IS DEAD AND DEPRECATED."))))


(defun newline-and-indent-relative ()
  (interactive)
  (newline)
  (indent-to-column (save-excursion
                      (forward-line -1)
                      (back-to-indentation)
                      (current-column))))

;;; ATS Parser

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.yats\\'" . ats-parser-mode))

;;;###autoload
(define-derived-mode ats-parser-mode ats-mode "ATS-Parser"
  "Major mode to edit ATS Parser source code.")

;;; ATS Lexer

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.lats\\'" . ats-lexer-mode))

;;;###autoload
(define-derived-mode ats-lexer-mode ats-mode "ATS-Lexer"
  "Major mode to edit ATS Lexer source code.")



(provide 'ats-mode)
;;; ats-mode.el ends here
