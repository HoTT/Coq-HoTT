From HoTT Require Import Basics.
From HoTT.Spaces.List Require Import Core Theory.

(** Here we check the universe levels of the lemmas from List.Core *)
Succeed Check list@{_}.
Succeed Check nil@{_}.
Succeed Check cons@{_}.
Succeed Check list_rect@{_ _}.
Succeed Check list_ind@{_ _}.
Succeed Check list_rec@{_ _}.
Succeed Check length@{_}.
Succeed Check app@{_}.
Succeed Check fold_left@{_ _}.
Succeed Check fold_right@{_ _}.
Succeed Check list_map@{_ _}.
Succeed Check list_map2@{_ _ _}.
Succeed Check reverse_acc@{_}.
Succeed Check reverse@{_}.
Succeed Check head@{_}.
Succeed Check tail@{_}.
Succeed Check last@{_}.
Succeed Check nth@{_}.
Succeed Check remove_last@{_}.
Succeed Check seq_rev@{}.
Succeed Check seq@{}.
Succeed Check repeat@{_}.
Succeed Check InList@{_}.
Succeed Check for_all@{_ _}.

(** Here we check the universe levels of the lemmas from List.Theory *)
Succeed Check length_0@{_}.
Succeed Check app_nil@{_}.
Succeed Check app_assoc@{_}.
Succeed Check list_pentagon@{_}.
Succeed Check length_app@{_}.
Succeed Check equiv_inlist_app@{_}.
Succeed Check fold_left_app@{_ _}.
Succeed Check fold_right_app@{_ _}.
Succeed Check length_list_map@{_ _}.
Succeed Check inlist_map@{_ _}.
Succeed Check inlist_map'@{_ _}.
Succeed Check list_map_id@{_}.
Succeed Check list_map_compose@{_ _ _}.
Succeed Check length_list_map2@{_ _ _}.
Succeed Check inlist_map2@{_ _ _}.
Succeed Check list_map2_repeat_l@{_ _ _}.
Succeed Check list_map2_repeat_r@{_ _ _}.
Succeed Check length_reverse_acc@{_}.
Succeed Check length_reverse@{_}.
Succeed Check list_map_reverse_acc@{_ _}.
Succeed Check list_map_reverse@{_ _}.
Succeed Check reverse_acc_cons@{_}.
Succeed Check reverse_cons@{_}.
Succeed Check nth_lt@{_}.
Succeed Check nth'@{_}.
Succeed Check nth'_nth'@{_}.
Succeed Check inlist_nth'@{_}.
Succeed Check nth_nth'@{_}.
Succeed Check nth'_cons@{_}.
Succeed Check index_of@{_}.
Succeed Check nth_list_map@{_ _}.
Succeed Check nth'_list_map@{_ _}.
Succeed Check nth'_list_map2@{_ _ _}.
Succeed Check nth'_repeat@{_}.
Succeed Check path_list_nth'@{_}.
Succeed Check nth_app@{_}.
Succeed Check nth_last@{_}.
Succeed Check last_app@{_}.
Succeed Check drop@{_}.
Succeed Check drop_0@{_}.
Succeed Check drop_1@{_}.
Succeed Check drop_nil@{_}.
Succeed Check drop_length_leq@{_}.
Succeed Check length_drop@{_}.
Succeed Check drop_inlist@{_}.
Succeed Check take@{_}.
Succeed Check take_0@{_}.
Succeed Check take_nil@{_}.
Succeed Check take_length_leq@{_}.
Succeed Check length_take@{_}.
Succeed Check take_inlist@{_}.
Succeed Check remove@{_}.
Succeed Check remove_0@{_}.
Succeed Check remove_length_leq@{_}.
Succeed Check length_remove@{_}.
Succeed Check remove_inlist@{_}.
Succeed Check length_seq_rev@{}.
Succeed Check length_seq@{}.
Succeed Check seq_rev_cons@{}.
Succeed Check seq_succ@{}.
Succeed Check seq_rev'@{}.
Succeed Check seq'@{}.
Succeed Check length_seq_rev'@{}.
Succeed Check length_seq'@{}.
Succeed Check seq_rev_seq_rev'@{}.
Succeed Check seq_seq'@{}.
Succeed Check nth_seq_rev@{}.
Succeed Check nth_seq@{}.
Succeed Check nth'_seq'@{}.
Succeed Check length_repeat@{_}.
Succeed Check inlist_repeat@{_}.
Succeed Check for_all_inlist@{_ _}.
Succeed Check inlist_for_all@{_ _}.
Succeed Check for_all_list_map@{_ _ _ _ _}.
Succeed Check for_all_list_map'@{_ _ _}.
Succeed Check for_all_list_map2@{_ _ _ _ _ _ _}.
Succeed Check for_all_list_map2'@{_ _ _ _ _ _ _}.
Succeed Check fold_left_preserves@{_ _ _ _ _}.
Succeed Check istrunc_for_all@{_ _}.
Succeed Check istrunc_for_all'@{_ _}.
Succeed Check for_all_repeat@{_ _}.
Succeed Check list_sigma@{_ _ _}.
Succeed Check length_list_sigma@{_ _ _}.
Succeed Check decidable_for_all@{_ _}.
