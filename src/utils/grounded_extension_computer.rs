use super::LabelType;
use crate::aa::{AAFramework, Argument};

pub(crate) fn grounded_extension<T>(af: &AAFramework<T>) -> Vec<&Argument<T>>
where
    T: LabelType,
{
    let max_arg_id = match af.max_argument_id() {
        Some(n) => n,
        None => return Vec::new(),
    };
    let mut ext = vec![];
    let mut n_processed_args = 0;
    let mut defeated_args = vec![false; 1 + max_arg_id];
    let mut attacked_by = vec![usize::MAX; 1 + max_arg_id];
    af.argument_set().iter().for_each(|arg| {
        let cnt = af.iter_attacks_to(arg).count();
        if cnt == 0 {
            ext.push(arg);
        }
        attacked_by[arg.id()] = cnt;
    });
    while n_processed_args < ext.len() {
        af.iter_attacks_from(ext[n_processed_args])
            .for_each(|defeating_att| {
                let defeated = defeating_att.attacked();
                if !defeated_args[defeated.id()] {
                    defeated_args[defeated.id()] = true;
                    af.iter_attacks_from(defeated).for_each(|defeated_att| {
                        let defended = defeated_att.attacked();
                        if attacked_by[defended.id()] == 1 {
                            ext.push(defended);
                        } else {
                            attacked_by[defended.id()] -= 1;
                        }
                    });
                }
            });
        n_processed_args += 1;
    }
    ext
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        aa::ArgumentSet,
        io::{AspartixReader, InstanceReader},
    };

    #[test]
    fn test_grounded_extension_1() {
        let arg_labels = vec!["a", "b", "c", "d", "e", "f"];
        let args = ArgumentSet::new_with_labels(&arg_labels);
        let mut af = AAFramework::new_with_argument_set(args);
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
        let mut af = AAFramework::new_with_argument_set(args);
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

    #[test]
    fn test_grounded_extension_after_arg_removal() {
        let instance = r#"
        arg(a).
        arg(b).
        arg(c).
        arg(d).
        att(a,b).
        att(b,c).
        att(c,d).
        "#;
        let reader = AspartixReader::default();
        let mut af = reader.read(&mut instance.as_bytes()).unwrap();
        let mut grounded_before = grounded_extension(&af)
            .iter()
            .map(|a| a.label().clone())
            .collect::<Vec<String>>();
        grounded_before.sort_unstable();
        assert_eq!(vec!["a", "c"], grounded_before);
        af.remove_argument(&"c".to_string()).unwrap();
        let mut grounded_after = grounded_extension(&af)
            .iter()
            .map(|a| a.label().clone())
            .collect::<Vec<String>>();
        grounded_after.sort_unstable();
        assert_eq!(vec!["a", "d"], grounded_after);
    }

    #[test]
    fn test_grounded_extension_empty_af() {
        let af = AAFramework::<usize>::default();
        assert!(grounded_extension(&af).is_empty());
    }
}
