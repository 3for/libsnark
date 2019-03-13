/** @file
 *****************************************************************************

 Implementation of functions to sample R1CS examples with prescribed parameters
 (according to some distribution).

 See r1cs_examples.hpp .

 *****************************************************************************
 * @author     This file is part of libsnark, developed by SCIPR Lab
 *             and contributors (see AUTHORS).
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/

#ifndef R1CS_EXAMPLES_TCC_
#define R1CS_EXAMPLES_TCC_

#include <cassert>

#include <libff/common/utils.hpp>

namespace libsnark {

template<typename FieldT>
r1cs_example<FieldT> generate_r1cs_example_with_field_input(const size_t num_constraints,
                                                            const size_t num_inputs)
{
    libff::enter_block("Call to generate_r1cs_example_with_field_input");

    assert(num_inputs <= num_constraints + 2);

    r1cs_constraint_system<FieldT> cs;
    cs.primary_input_size = num_inputs;
    cs.auxiliary_input_size = 2 + num_constraints - num_inputs; // TODO: explain this

    r1cs_variable_assignment<FieldT> full_variable_assignment;
    FieldT a = FieldT::random_element();
    FieldT b = FieldT::random_element();
    full_variable_assignment.push_back(a);
    full_variable_assignment.push_back(b);

    for (size_t i = 0; i < num_constraints-1; ++i)
    {
        linear_combination<FieldT> A, B, C;

        if (i % 2)
        {
            // a * b = c
            A.add_term(i+1, 1);
            B.add_term(i+2, 1);
            C.add_term(i+3, 1);
            FieldT tmp = a*b;
            full_variable_assignment.push_back(tmp);
            a = b; b = tmp;
        }
        else
        {
            // a + b = c
            B.add_term(0, 1);
            A.add_term(i+1, 1);
            A.add_term(i+2, 1);
            C.add_term(i+3, 1);
            FieldT tmp = a+b;
            full_variable_assignment.push_back(tmp);
            a = b; b = tmp;
        }

        cs.add_constraint(r1cs_constraint<FieldT>(A, B, C));
    }

    linear_combination<FieldT> A, B, C;
    FieldT fin = FieldT::zero();
    for (size_t i = 1; i < cs.num_variables(); ++i)
    {
        A.add_term(i, 1);
        B.add_term(i, 1);
        fin = fin + full_variable_assignment[i-1];
    }
    C.add_term(cs.num_variables(), 1);
    cs.add_constraint(r1cs_constraint<FieldT>(A, B, C));
    full_variable_assignment.push_back(fin.squared());

    /* split variable assignment */
    r1cs_primary_input<FieldT> primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + num_inputs);
    r1cs_primary_input<FieldT> auxiliary_input(full_variable_assignment.begin() + num_inputs, full_variable_assignment.end());

    /* sanity checks */
    assert(cs.num_variables() == full_variable_assignment.size());
    assert(cs.num_variables() >= num_inputs);
    assert(cs.num_inputs() == num_inputs);
    assert(cs.num_constraints() == num_constraints);
    assert(cs.is_satisfied(primary_input, auxiliary_input));

    libff::leave_block("Call to generate_r1cs_example_with_field_input");

    return r1cs_example<FieldT>(std::move(cs), std::move(primary_input), std::move(auxiliary_input));
}

template<typename FieldT>
r1cs_example<FieldT> generate_r1cs_example_with_binary_input(const size_t num_constraints,
                                                             const size_t num_inputs)
{
    libff::enter_block("Call to generate_r1cs_example_with_binary_input");

    assert(num_inputs >= 1);

    r1cs_constraint_system<FieldT> cs;
    cs.primary_input_size = num_inputs; //public 100
    cs.auxiliary_input_size = num_constraints; /* we will add one auxiliary variable per constraint */ //private 1000

    r1cs_variable_assignment<FieldT> full_variable_assignment;
    for (size_t i = 0; i < num_inputs; ++i) //full_variable_assignment中0~99为primary_input(public)
    {
        full_variable_assignment.push_back(FieldT(std::rand() % 2));
    }

    size_t lastvar = num_inputs-1; //full_variable_assignment中0~99为primary_input(public),100~1099为auxiliary_input(private)
    for (size_t i = 0; i < num_constraints; ++i) //1000
    {
        ++lastvar; //此时lastvar=100
        const size_t u = (i == 0 ? std::rand() % num_inputs : std::rand() % i); //i==0时，u的取值为0~99；i>0时，u的取值为0~i。【i的取值范围为0~999】
        const size_t v = (i == 0 ? std::rand() % num_inputs : std::rand() % i); //i==0时，v的取值为0~99；i>0时，v的取值为0~i。【i的取值范围为0~999】

        /* chose two random bits and XOR them together:
           res = u + v - 2 * u * v
           2 * u * v = u + v - res
        */
        // u XOR v = u + v - 2 * u * v
        linear_combination<FieldT> A, B, C;
        A.add_term(u+1, 2);//const variable<FieldT> &var, const integer_coeff_t int_coeff //2*x_aj, 其中aj=u+1>0。【aj的取值范围为1~1000】
        B.add_term(v+1, 1);//1*x_bj，其中bj=v+1>0。【bj的取值范围为1~1000】
        if (u == v)
        {
            C.add_term(u+1, 2); //若u==v，即x_bj==x_aj，此时2*x_aj
        }
        else
        {
            C.add_term(u+1, 1); 
            C.add_term(v+1, 1);//u+v,若u!=v，则为x_aj+x_bj
        }
        C.add_term(lastvar+1, -FieldT::one()); //此时x_cj=lastvar+1=101+i。【cj的取值范围为101~1100】,-1*x_cj

        cs.add_constraint(r1cs_constraint<FieldT>(A, B, C));
        full_variable_assignment.push_back(full_variable_assignment[u] + full_variable_assignment[v] - full_variable_assignment[u] * full_variable_assignment[v] - full_variable_assignment[u] * full_variable_assignment[v]);
    }

    /* split variable assignment */////full_variable_assignment中0~99为primary_input(public),100~1099为auxiliary_input(private)
    r1cs_primary_input<FieldT> primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + num_inputs);
    r1cs_primary_input<FieldT> auxiliary_input(full_variable_assignment.begin() + num_inputs, full_variable_assignment.end());

    /* sanity checks */
    assert(cs.num_variables() == full_variable_assignment.size()); //共1100个varibale
    assert(cs.num_variables() >= num_inputs);
    assert(cs.num_inputs() == num_inputs); //primary_input_size为100
    assert(cs.num_constraints() == num_constraints); //共1000个 r1cs constraint
    assert(cs.is_satisfied(primary_input, auxiliary_input));

    libff::leave_block("Call to generate_r1cs_example_with_binary_input");

    return r1cs_example<FieldT>(std::move(cs), std::move(primary_input), std::move(auxiliary_input));
}

} // libsnark

#endif // R1CS_EXAMPLES_TCC
