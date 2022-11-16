use crate::{
    aa::{AAFramework, Argument, LabelType},
    sat::Assignment,
};

// Translates a SAT solver assignment related to a connected component to the corresponding subset of arguments of the initial AF.
pub(crate) fn cc_assignment_to_init_af_extension<'a, T, F>(
    assignment: Assignment,
    cc_af: &AAFramework<T>,
    init_af: &'a AAFramework<T>,
    cc_arg_id_from_solver_var: F,
) -> Vec<&'a Argument<T>>
where
    T: LabelType,
    F: Fn(usize) -> Option<usize>,
{
    assignment
        .iter()
        .filter(|(_, val)| val.unwrap_or(false))
        .filter_map(|(var, _)| cc_arg_id_from_solver_var(var))
        .map(|cc_arg_id| {
            cc_arg_to_init_af_arg(cc_af.argument_set().get_argument_by_id(cc_arg_id), init_af)
        })
        .collect()
}

pub(crate) fn cc_arg_to_init_af_arg<'a, 'b, T>(
    cc_arg: &'a Argument<T>,
    init_af: &'b AAFramework<T>,
) -> &'b Argument<T>
where
    T: LabelType,
{
    init_af.argument_set().get_argument(cc_arg.label()).unwrap()
}
