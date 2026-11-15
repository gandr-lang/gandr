#[macro_export]
macro_rules! async_scope {
    (| $scope:ident | -> $out_ty:ty { $($body:tt)* }) => {{
        $crate::async_scope!(self { } |$scope| -> $out_ty { $($body)* })
    }};
    ($self:ident { $($field_name:ident : $field_ty:ty),* $(,)? } | $scope:ident | -> $out_ty:ty { $($body:tt)* }) => {{
        struct Closure<'env> {
            $($field_name : $field_ty,)*
            phd_env: ::core::marker::PhantomData<&'env mut &'env ()>,
        }
        impl<'env> Closure<'env> {
            fn new($($field_name : $field_ty),*) -> Self {
                Self {
                    $($field_name,)*
                    phd_env: ::core::marker::PhantomData,
                }
            }
        }
        impl<'env> RuntimeClosure<'env, $out_ty> for Closure<'env> {
            async fn call<'tsk>($self, $scope: &'tsk Scope<'tsk, 'env>) -> $out_ty {
                $($body)*
            }
        }
        Closure::new($($field_name),*)
    }};
}
