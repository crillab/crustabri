use crate::{AAFramework, Argument, LabelType};

/// Computes the grounded extension of an AF.
pub fn grounded_extension<T>(af: &AAFramework<T>) -> Vec<&Argument<T>>
where
    T: LabelType,
{
    let mut ext = vec![];
    let mut n_processed_args = 0;
    let mut defeated_args = vec![false; af.n_arguments()];
    let mut attacked_by = af
        .attacks_to()
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let n = v.len();
            if n == 0 {
                ext.push(af.argument_set().get_argument_by_id(i))
            }
            n
        })
        .collect::<Vec<usize>>();
    let attacks = af.attacks();
    while n_processed_args < ext.len() {
        let id = ext[n_processed_args].id();
        af.attack_ids_from(id).iter().for_each(|defeating_att| {
            let (_, defeated) = attacks[*defeating_att];
            if !defeated_args[defeated] {
                defeated_args[defeated] = true;
                af.attack_ids_from(defeated).iter().for_each(|att| {
                    let (_, attacked) = attacks[*att];
                    if attacked_by[attacked] == 1 {
                        ext.push(af.argument_set().get_argument_by_id(attacked))
                    } else {
                        attacked_by[attacked] -= 1;
                    }
                })
            }
        });
        n_processed_args += 1;
    }
    ext
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ArgumentSet;

    #[test]
    fn test_grounded_extension_1() {
        let arg_labels = vec!["a", "b", "c", "d", "e", "f"];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut af = AAFramework::new(args);
        af.new_attack(&"a", &"b").unwrap();
        af.new_attack(&"b", &"c").unwrap();
        af.new_attack(&"b", &"d").unwrap();
        af.new_attack(&"c", &"e").unwrap();
        af.new_attack(&"d", &"e").unwrap();
        af.new_attack(&"e", &"f").unwrap();
        let mut grounded = grounded_extension(&af)
            .iter()
            .map(|a| *a.label())
            .collect::<Vec<&str>>();
        grounded.sort_unstable();
        assert_eq!(vec!["a", "c", "d", "f"], grounded)
    }

    #[test]
    fn test_grounded_extension_2() {
        let arg_labels = vec!["x", "a", "b", "c", "d", "e", "f"];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut af = AAFramework::new(args);
        af.new_attack(&"x", &"a").unwrap();
        af.new_attack(&"a", &"b").unwrap();
        af.new_attack(&"b", &"c").unwrap();
        af.new_attack(&"b", &"d").unwrap();
        af.new_attack(&"c", &"e").unwrap();
        af.new_attack(&"d", &"e").unwrap();
        af.new_attack(&"e", &"f").unwrap();
        let mut grounded = grounded_extension(&af)
            .iter()
            .map(|a| *a.label())
            .collect::<Vec<&str>>();
        grounded.sort_unstable();
        assert_eq!(vec!["b", "e", "x"], grounded)
    }
}
