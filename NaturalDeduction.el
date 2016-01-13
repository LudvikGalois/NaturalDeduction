;;;; A natural deduction assistant written in emacs lisp
;;;; Copyright Robert 'Probie' Offner 2015
;;;; Sorry it's pretty hacky - I wrote most of it in a moving car
;;;; without quite knowing the syntax (or semantics) of what this
;;;; was meant to do.

(require 'cl)

(defun nat-ded-make-var (varname)
  "Turn a string into a natural deduction variable"
  (cons 'var varname))

(defun nat-ded-make-bin-op (op p q)
  "Make a binary op"
  (cons op (cons p q)))

(defun nat-ded-make-and (p q)
  "Make an and clause"
  (nat-ded-make-bin-op 'and p q))

(defun nat-ded-make-or (p q)
  "Make an or clause"
  (nat-ded-make-bin-op 'or p q))

(defun nat-ded-make-imp (p q)
  "Make an implication clause"
  (nat-ded-make-bin-op 'imp p q))

(defun nat-ded-make-not (p)
  "Make a negation"
  (cons 'not p))

(defun nat-ded-make-bot ()
  "Make bottom"
  (cons 'bot nil))

(defun nat-ded-parens (p str)
  "Add parens around a string"
  (if p (concat "(" str ")") str))

(defun nat-ded-show-bin-op (opstr opassoc p q assoc)
  " convert a binary op to a string"
  (nat-ded-parens (< opassoc assoc)
                  (concat (nat-ded-show-line p (1+ opassoc))
                          opstr (nat-ded-show-line q opassoc))))

(defun nat-ded-show-line (prop &optional assoc)
  "Convert a line of proof into a string"
  (let ((type (car prop))
        (val (cdr prop))
        (assoc (if assoc assoc 0))) ;; If not given, set assoc to 0
    (cond ((eq type 'var) val)
          ((eq type 'and) (nat-ded-show-bin-op "∧" 3 (car val) (cdr val) assoc))
          ((eq type 'or) (nat-ded-show-bin-op "∨" 2 (car val) (cdr val) assoc))
          ((eq type 'imp) (nat-ded-show-bin-op "⇒" 1 (car val) (cdr val) assoc))
          ((eq type 'not) (concat "¬" (nat-ded-show-line val 4)))
          ((eq type 'bot) "⊥"))))

(defun nat-ded-all-but-last (sequence)
  (if (eq (cdr sequence) nil) nil (cons (car sequence)
                                        (nat-ded-all-but-last (cdr sequence)))))

(defun nat-ded-delete-line ()
  "Delete the last line of proof"
  (interactive)
  (when (< 1 nat-ded-proof-line)
    (setq nat-ded-proof-line (1- nat-ded-proof-line))
    (setq nat-ded-proof (vconcat (nat-ded-all-but-last (append nat-ded-proof nil))))
    (nat-ded-redraw-proof)))

(defun nat-ded-assumption ()
  "Make an assumption"
  (interactive)
  (nat-ded-make-proof-line (nat-ded-read-formula) 'assumption
                           (list nat-ded-proof-line))
  (nat-ded-redraw-proof))

(defun nat-ded-assumptions-at (line)
  (cadddr (elt nat-ded-proof (1- line))))

(defun nat-ded-form-at (line)
  (cadr (elt nat-ded-proof (1- line))))

(defun nat-ded-rule-at (line)
  (caddr (elt nat-ded-proof (1- line))))

(defun nat-ded-assump-union (assump1 assump2)
  "Union two sets of assumptions, preserving order"
  (sort (union (copy-list assump1) (copy-list assump2)) '>))

(defun nat-ded-intro ()
  (interactive)
  (let ((key (read-key "Press a for ∧I, o for ∨I, i for ⇒I, n for ¬I or ~ for ¬¬I")))
    (cond ((= ?a key) (nat-ded-and-intro))
          ((= ?o key) (nat-ded-or-intro))
          ((= ?i key) (nat-ded-imp-intro)) 
          ((= ?n key) (nat-ded-not-intro))
          ((= ?~ key) (nat-ded-double-neg-intro))
          ((= 27 key) (error "User cancelled input"))
          (t nil))))

(defun nat-ded-elim ()
  (interactive)
  (let ((key (read-key "Press a for ∧E, o for ∨E, i for ⇒E, n for ¬E or ~ for ¬¬E")))
    (cond ((= ?a key) (nat-ded-and-elim))
          ((= ?o key) (nat-ded-or-elim))
          ((= ?i key) (nat-ded-imp-elim)) 
          ((= ?n key) (nat-ded-not-elim))
          ((= ?~ key) (nat-ded-double-neg-elim))
          ((= 27 key) (error "User cancelled input"))
          (t nil)))) 


(defun nat-ded-and-intro ()
  "Introduce an and from two lines of the proof"
  (let ((line1 (read-number "Insert the first line: "))
        (line2 (read-number "Insert the second line: ")))
    (nat-ded-make-proof-line (nat-ded-make-and (nat-ded-form-at line1)
                                               (nat-ded-form-at line2))
                             (list 'andI line1 line2)
                             (nat-ded-assump-union (nat-ded-assumptions-at line1)
                                                   (nat-ded-assumptions-at line2))))
  (nat-ded-redraw-proof))

(defun nat-ded-and-elim ()
  "Grab the left side of an and"
  (let ((line (read-number "Which line would you like to perform ∧E on?: ")))
    (if (eq 'and (car (nat-ded-form-at line)))
        (nat-ded-make-proof-line
         (if (eq ?l (read-key "Press 'l' for the left side, or 'r' for the right side"))
             (cadr (nat-ded-form-at line)) (cddr (nat-ded-form-at line)))
         (list 'andE line) (nat-ded-assumptions-at line))))
  (nat-ded-redraw-proof))

(defun nat-ded-or-intro ()
  "Or introduction"
  (let ((line (read-number "Line for ∨I: ")))
    (let ((key (read-key "Press 'l' to introduce on the left, or any other key to introduce on the right")))
      (nat-ded-make-proof-line
       (if (= ?l key) (nat-ded-make-or (nat-ded-read-formula) (nat-ded-form-at line))
         (nat-ded-make-or (nat-ded-form-at line) (nat-ded-read-formula)))
       (list 'orI line) (nat-ded-assumptions-at line))))
  (nat-ded-redraw-proof))

;;; Yuck
(defun nat-ded-or-elim ()
  "Perform or elimination"
  (let ((line (read-number "Line which contains ∨: ")))
    (if (eq 'or (car (nat-ded-form-at line)))
        (let ((left-conc (read-number "Conclusion for LHS: "))
              (left-assump
               (read-number (format "%s which is an assumption for LHS conclusion: "
                                    (nat-ded-show-line (cadr (nat-ded-form-at line)))))))
          (if (and (nat-ded-eq (cadr (nat-ded-form-at line)) (nat-ded-form-at left-assump))
                   (member left-assump (nat-ded-assumptions-at left-conc)))
              (let ((right-conc (read-number "Conclusion for RHS: "))
                    (right-assump
                     (read-number (format "%s which is an assumption for RHS conclusion: "
                                          (nat-ded-show-line (cddr (nat-ded-form-at line)))))))
                (if (and (nat-ded-eq (cddr (nat-ded-form-at line)) (nat-ded-form-at right-assump))
                         (member right-assump (nat-ded-assumptions-at right-conc)))
                    (if (nat-ded-eq (nat-ded-form-at left-conc) (nat-ded-form-at right-conc))
                        (nat-ded-make-proof-line
                         (nat-ded-form-at left-conc)
                         (list 'orE line left-conc left-assump right-conc right-assump)
                         (nat-ded-assump-union
                          (nat-ded-assumptions-at line)
                          (nat-ded-assump-union (remove left-assump
                                                        (nat-ded-assumptions-at left-conc))
                                                (remove right-assump
                                                        (nat-ded-assumptions-at right-conc)))))
                      (message "The conclusion %s and %s don't match"
                               (nat-ded-show-line (nat-ded-form-at left-conc))
                               (nat-ded-show-line (nat-ded-form-at right-conc))))
                  (message "%s is not %s, or it's not an assumption"
                           (nat-ded-show-line (cddr (nat-ded-form-at line)))
                           (nat-ded-show-line (nat-ded-form-at right-assump)))))
            (message "%s is not %s, or it's not an assumption"
                     (nat-ded-show-line (cadr (nat-ded-form-at line)))
                     (nat-ded-show-line (nat-ded-form-at left-assump)))))
      (message "%s is not an ∨" (nat-ded-show-line (nat-ded-form-at line)))))
  (nat-ded-redraw-proof))

(defun nat-ded-antecedant (line)
  "Find the antecedent of an implication"
  (let ((form (nat-ded-form-at line)))
    (if (eq (car form) 'imp) (cadr form))))

(defun nat-ded-consequent (line)
  (let ((form (nat-ded-form-at line)))
    (if (eq (car form) 'imp) (cddr form))))

(defun nat-ded-imp-elim ()
  "Modus ponens"
  (let ((implication (read-number "Line which contains ⇒: "))
        (line (read-number "Line with discharging rule: ")))
    (if (nat-ded-eq (nat-ded-form-at line) (nat-ded-antecedant implication))
        (nat-ded-make-proof-line (nat-ded-consequent implication)
                                 (list 'impE implication line)
                                 (nat-ded-assump-union (nat-ded-assumptions-at implication)
                                                       (nat-ded-assumptions-at line)))
      (message "%s not equal to %s"
               (nat-ded-show-line (nat-ded-antecedant implication))
               (nat-ded-show-line (nat-ded-form-at line)))))
  (nat-ded-redraw-proof))

(defun nat-ded-imp-intro ()
  "Implication introduction"
  (let ((line (read-number "Line for ⇒I: "))
        (imp-line (read-number "With which assumption? ")))
    (if (eq 'assumption (nat-ded-rule-at imp-line))
        (let ((new-assumptions (nat-ded-assump-union (nat-ded-assumptions-at line)
                                                     (nat-ded-assumptions-at imp-line))))
          (nat-ded-make-proof-line
           (nat-ded-make-imp (nat-ded-form-at imp-line) (nat-ded-form-at line))
           (list 'impI (if (member imp-line (nat-ded-assumptions-at line)) imp-line nil) line)
           (remove imp-line new-assumptions)))
      (let ((new-assumptions (nat-ded-assump-union (nat-ded-assumptions-at line)
                                                   (nat-ded-assumptions-at imp-line))))
        (nat-ded-make-proof-line
         (nat-ded-make-imp (nat-ded-form-at imp-line) (nat-ded-form-at line))
         (list 'impI nil line)
         new-assumptions))))
  (nat-ded-redraw-proof))

(defun nat-ded-not-intro ()
  "Negation introduction"
  (let ((line (read-number "Line with ⊥: "))
        (imp-line (read-number "With which assumption? ")))
    (if (and (eq 'assumption (nat-ded-rule-at imp-line))
             (eq 'bot (car (nat-ded-form-at line))))
        (nat-ded-make-proof-line
         (nat-ded-make-not (nat-ded-form-at imp-line))
         (list 'notI imp-line line)
         (remove imp-line (nat-ded-assump-union (nat-ded-assumptions-at line)
                                                (nat-ded-assumptions-at imp-line))))
      (message "%d is not an assumption, or %d is not ⊥" imp-line line)))
  (nat-ded-redraw-proof))

(defun nat-ded-not-elim ()
  "Introduce ⊥"
  (interactive)
  (let ((line1 (read-number "Insert the first line: "))
        (line2 (read-number "Insert the second line: ")))
    (if (or (nat-ded-contradiction (nat-ded-make-and (nat-ded-form-at line1)
                                                     (nat-ded-form-at line2)))
            (nat-ded-contradiction (nat-ded-make-and (nat-ded-form-at line2)
                                                     (nat-ded-form-at line1))))
        (nat-ded-make-proof-line (nat-ded-make-bot)
                                 (cons 'notE (sort (list line1 line2) '>))
                                 (nat-ded-assump-union (nat-ded-assumptions-at line1)
                                                       (nat-ded-assumptions-at line2)))
      (message "%s is not a contradiction"
               (nat-ded-show-line
                (nat-ded-make-and (nat-ded-form-at line1)
                                  (nat-ded-form-at line2))))))
  (nat-ded-redraw-proof))

(defun nat-ded-raa ()
  "Use RAA"
  (interactive)
   (let* ((line1 (read-number "Insert the first line: "))
          (line2 (read-number "Insert the second line: "))
          (existingp (y-or-n-p "Are we discharging an existing line? "))
          (new-assumptions (nat-ded-assump-union (nat-ded-assumptions-at line1)
                                                (nat-ded-assumptions-at line2))))
     (if (or (nat-ded-contradiction (nat-ded-make-and (nat-ded-form-at line1)
                                                      (nat-ded-form-at line2)))
             (nat-ded-contradiction (nat-ded-make-and (nat-ded-form-at line2)
                                                      (nat-ded-form-at line1))))
         (if existingp (let ((line3 (read-number "Insert line to discharge: ")))
                         (nat-ded-make-proof-line (nat-ded-make-not (nat-ded-form-at line3))
                                                  (cons 'RAA (cons (if (and (eq 'assumption (nat-ded-rule-at line3))
                                                                            (member line3 new-assumptions))
                                                                       line3)
                                                                   (sort (list line1 line2) '>)))
                                                  (remove line3 (nat-ded-assump-union
                                                                 (nat-ded-assumptions-at line3)
                                                                 new-assumptions))))
           (nat-ded-make-proof-line (nat-ded-make-not (nat-ded-read-formula))
                                    (cons 'RAA (cons nil (sort (list line1 line2) '>)))
                                    new-assumptions))
       (message "%s is not a contradiction"
                (nat-ded-show-line
                 (nat-ded-make-and (nat-ded-form-at line1)
                                   (nat-ded-form-at line2))))))
   (nat-ded-redraw-proof)) 

(defun nat-ded-contradiction (formula)
  "Is a formula a contradiction?"
  (let ((type (car formula))
        (val (cdr formula)))
    (and (eq type 'and)
         (or (nat-ded-eq (nat-ded-make-not (car val)) (cdr val))
             (nat-ded-eq (cdr val) (nat-ded-make-not (car val)))))))

(defun nat-ded-eq (form1 form2)
  "Are two formulas equal?"
  (let ((type1 (car form1))
        (val1 (cdr form1))
        (type2 (car form2))
        (val2 (cdr form2)))
    (and (eq type1 type2)
         (cond ((eq type1 'var) (string= val1 val2))
               ((eq type1 'not) (nat-ded-eq val1 val2))
               (t (and (nat-ded-eq (car val1) (car val2))
                       (nat-ded-eq (cdr val1) (cdr val2))))))))

(defun nat-ded-double-neg-p (formula)
  (and (eq (car formula) 'not) (eq (cadr formula) 'not)))  

(defun nat-ded-double-neg-elim ()
  "Double negation elimination"
  (let ((line (read-number "Line which contains double negation: ")))
    (if (nat-ded-double-neg-p (nat-ded-form-at line))
        (nat-ded-make-proof-line
         (cddr (nat-ded-form-at line))
         (list 'nnE line) (nat-ded-assumptions-at line))
      (message "%s is not a double negation" (nat-ded-show-line (nat-ded-form-at line)))))
  (nat-ded-redraw-proof))

(defun nat-ded-double-neg-intro ()
  "Double negation Introduction"
  (let ((line (read-number "Line for ¬¬I: ")))
    (nat-ded-make-proof-line
         (nat-ded-make-not (nat-ded-make-not (nat-ded-form-at line)))
         (list 'nnI line) (nat-ded-assumptions-at line)))
  (nat-ded-redraw-proof))

(defun nat-ded-read-var (acc display-left display-right)
  "Read a variable, terminated by RET"
  (let ((key (read-key (concat display-left "<" (reverse acc) ">" display-right))))
    (if (= 27 key) (error "Input cancelled by user")
      (if (= 127 key)
          (nat-ded-read-var (if acc (cdr acc) nil) display-left display-right)
        (if (or (= 13 key) (= 32 key) (= 9 key))
            (if acc (nat-ded-make-var (apply 'string (reverse acc)))
              (nat-ded-read-var acc display-left display-right))
          (nat-ded-read-var (cons key acc) display-left display-right))))))

(defun nat-ded-input-bin-op (fun opstr display-left display-right)
  "Helper function to reduce code duplication - do not call externally"
  (let ((lhs (nat-ded-input-formula (concat display-left "(")
                                    (concat opstr "_)" display-right))))
    (funcall fun
     lhs
     (nat-ded-input-formula (concat display-left "(" (nat-ded-show-line lhs) opstr)
                            (concat ")" display-right)))))

(defun nat-ded-input-formula (display-left display-right)
  "Read a formula in from the keyboard"
     (let ((key (read-key
                      (if (not (and (string= "" display-left) (string= "" display-right)))
                          (concat display-left "_" display-right)
                        "Press a for ∧, o for ∨, i for ⇒, n for ¬ and v for a var"))))
       (cond ((= ?a key) (nat-ded-input-bin-op 'nat-ded-make-and "∧" display-left display-right))
             ((= ?o key) (nat-ded-input-bin-op 'nat-ded-make-or "∨" display-left display-right))
             ((= ?i key) (nat-ded-input-bin-op 'nat-ded-make-imp "⇒" display-left display-right)) 
             ((= ?n key) (nat-ded-make-not (nat-ded-input-formula (concat display-left "¬") display-right)))
             ((= ?v key) (nat-ded-read-var nil display-left display-right))
             ((= 27 key) (error "User cancelled input"))
             (t (nat-ded-input-formula display-left display-right)))))

(defun nat-ded-read-formula ()
  "Let the user input a formula"
  (nat-ded-input-formula "" ""))

(defun natural-deduction-proof ()
  "Make a buffer for writing proofs"
  (interactive)
  (nat-ded-redraw-proof))

(defvar nat-ded-mode-map
  (let ((map (make-sparse-keymap 'nat-ded-mode-map)))
    (define-key map "a" 'nat-ded-assumption)
    (define-key map "d" 'nat-ded-delete-line)
    (define-key map "i" 'nat-ded-intro)
    (define-key map "e" 'nat-ded-elim)
    (define-key map "r" 'nat-ded-raa)
    (define-key map "h" 'nat-ded-help)
    (define-key map "n" 'nat-ded-new)
    (define-key map "s" 'nat-ded-save)
    (define-key map "l" 'nat-ded-load)
    (define-key map "x" 'nat-ded-export)
    map))

;;; Pretty much every function calls this. This means every operation would
;;; be slow for really long proofs, but if you're writing long proof, hopefully
;;; you're using a nicer system than this
(defun nat-ded-redraw-proof ()
  "Redraw the proof"
  (switch-to-buffer (get-buffer-create "*NatDedProof*"))
  (nat-ded-mode)
  (setq buffer-read-only t)
  (let ((buffer-read-only nil))
    (erase-buffer)
    (insert (nat-ded-proof-string))))

(defun nat-ded-make-proof-line (formula reason assumptions)
  (let ((new-line (list nat-ded-proof-line formula reason assumptions)))
    (setq nat-ded-proof-line (1+ nat-ded-proof-line))
    (setq nat-ded-proof (vconcat nat-ded-proof (list new-line)))))

;;; I could probably allow multiple natural deduction proofs if these
;;; were buffer local, but then I'd need a more sane nat-ded-redraw-proof
(defvar nat-ded-proof [])
(defvar nat-ded-proof-line 1)

(defun nat-ded-new-proof ()
  (setq nat-ded-proof [])
  (setq nat-ded-proof-line 1)
  t)

(defun nat-ded-reason-to-string (reason)
  (cond ((eq reason 'assumption) "A")
        ((eq (car reason) 'andI) (format "%d,%d ∧I" (cadr reason) (caddr reason)))
        ((eq (car reason) 'orI) (format "%d ∨I" (cadr reason)))
        ((eq (car reason) 'impI) (if (cadr reason)
                                     (format "%d[%d] ⇒I" (caddr reason) (cadr reason))
                                   (format "%d[] ⇒I" (caddr reason))))
        ((eq (car reason) 'notI) (format "%d[%d] ¬I" (caddr reason) (cadr reason)))
        ((eq (car reason) 'notE) (format "%d,%d ¬E" (caddr reason) (cadr reason)))
        ((eq (car reason) 'impE) (format "%d,%d ⇒E" (cadr reason) (caddr reason)))
        ((eq (car reason) 'andE) (format "%d ∧E" (cadr reason)))
        ((eq (car reason) 'nnE) (format "%d ¬¬E" (cadr reason)))
        ((eq (car reason) 'nnI) (format "%d ¬¬I" (cadr reason)))
        ((eq (car reason) 'RAA) (if (cadr reason)
                                    (format "%d,%d[%d] RAA" (cadddr reason) (caddr reason) (cadr reason))
                                  (format "%d,%d[] RAA" (cadddr reason) (caddr reason))))
        ((eq (car reason) 'orE) (format "%d, %d[%d], %d[%d] ∨E"
                                        (elt reason 1)
                                        (elt reason 2)
                                        (elt reason 3)
                                        (elt reason 4) ;; no caddddr :'(
                                        (elt reason 5)))
        (t "Unknown")))

(defun nat-ded-proof-line-string (line)
  (let ((linenum (car line))
        (formula (cadr line))
        (reason (caddr line))
        (assumptions (reverse (cadddr line))))
    (format "%11s %-5s %-50s %s\n"
            (nat-ded-assumptions-string assumptions)
            (concat "(" (number-to-string linenum) ")") 
            (nat-ded-show-line formula) 
            (nat-ded-reason-to-string reason))))

(defun nat-ded-proof-string ()
  (format "Probie's Natural Deduction Proof Assistant (Press 'h' for help)\n\n%-11s %-5s %-50s %s\n%s\n%s%s\n%s\n"
          "Assumptions" "Line" "Forumla" "Rule" 
          (concat (make-vector 85 ?-))
          ;; There's probably a better way to repeat a character, but meh
          (apply 'concat (mapcar 'nat-ded-proof-line-string nat-ded-proof))
          (concat (make-vector 85 ?-))
          (if (< nat-ded-proof-line 2) "" (nat-ded-show-conclusion (elt nat-ded-proof (- nat-ded-proof-line 2))))))

(defun nat-ded-assumptions-string (assumps)
  (cond ((eq nil assumps) "")
        ((eq nil (cdr assumps)) (number-to-string (car assumps)))
        (t (concat (number-to-string (car assumps)) ","
                   (nat-ded-assumptions-string (cdr assumps))))))

(defun nat-ded-assumptions-form-string (assumptions)
  (cond ((eq nil assumptions) "")
        ((eq nil (cdr assumptions)) (nat-ded-show-line (nat-ded-form-at (car assumptions))))
        (t (concat (nat-ded-show-line (nat-ded-form-at (car assumptions))) ","
                   (nat-ded-assumptions-form-string (cdr assumptions))))))

(defun nat-ded-show-conclusion (line)
  (let ((assumptions (reverse (cadddr line)))
        (formula (cadr line)))
    (format "%s ⊢ %s" 
            (nat-ded-assumptions-form-string assumptions)
            (nat-ded-show-line formula))))

(defun nat-ded-help ()
  (interactive)
  (message "%s" (concat "Press 'a' for an assumption, 'i' to introduce something, "
                        "'e' to eliminate something, 'r' for RAA or 'd' to delete a line.\n"
                        "Press 's' to save, 'l' to load, 'x' to export, or 'n' to start a new proof.")))

(defun nat-ded-save ()
  (interactive)
  (with-temp-file (read-file-name "File to save to: ")
    (prin1 nat-ded-proof (current-buffer))
    (prin1 nat-ded-proof-line (current-buffer))))

(defun nat-ded-load ()
  (interactive)
  (with-temp-buffer
    (insert-file-contents (read-file-name "File to load from: "))
    (goto-char (point-min))
    (setq nat-ded-proof (read (current-buffer)))
    (setq nat-ded-proof-line (read (current-buffer))))
  (nat-ded-redraw-proof))

(defun nat-ded-export-string ()
  (let ((proof-heading
         (if (< nat-ded-proof-line 2) "" (nat-ded-show-conclusion
                                          (elt nat-ded-proof (- nat-ded-proof-line 2))))))
    (format "%s%s%s\n%s"
            (concat (make-vector (max 0 (/ (- 85 (length proof-heading)) 2)) ?\s))
            proof-heading
            (concat (make-vector (max 0 (/ (- 86 (length proof-heading)) 2)) ?\s))
            (apply 'concat (mapcar 'nat-ded-proof-line-string nat-ded-proof)))))

(defun nat-ded-export ()
  (interactive)
  (with-temp-file (read-file-name "File to export to:")
    (insert (nat-ded-export-string))))

(defun nat-ded-new ()
  (interactive)
  (when (y-or-n-p "Really start a new proof")
    (nat-ded-new-proof)
    (nat-ded-redraw-proof)))

(defvar nat-ded-mode-hook nil)

(defun nat-ded-mode ()
  "Natural Deduction Mode"
  (interactive)
  (kill-all-local-variables)
  (use-local-map nat-ded-mode-map)
  (setq major-mode 'nat-ded-mode)
  (setq mode-name "Natural-Deduction")
  (run-hooks 'nat-ded-mode-hook))

(provide 'nat-ded-mode)

;;; For those who use evil (because emacs does contain a proper text editor
;;; these days)
(if (fboundp 'evil-set-initial-state) (evil-set-initial-state 'nat-ded-mode 'emacs))
