/*-------------------------------------------------------------------------
 *
 * rangetypes_typanalyze.c
 *	  Functions for gathering statistics from range columns
 *
 * For a range type column, histograms of lower and upper bounds, and
 * the fraction of NULL and empty ranges are collected.
 *
 * Both histograms have the same length, and they are combined into a
 * single array of ranges. This has the same shape as the histogram that
 * std_typanalyze would collect, but the values are different. Each range
 * in the array is a valid range, even though the lower and upper bounds
 * come from different tuples. In theory, the standard scalar selectivity
 * functions could be used with the combined histogram.
 *
 * Portions Copyright (c) 1996-2020, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/utils/adt/rangetypes_typanalyze.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "catalog/pg_operator.h"
#include "commands/vacuum.h"
#include "utils/float.h"
#include "utils/fmgrprotos.h"
#include "utils/lsyscache.h"
#include "utils/rangetypes.h"

static int	float8_qsort_cmp(const void *a1, const void *a2);
static int	range_bound_qsort_cmp(const void *a1, const void *a2, void *arg);
static void compute_range_stats(VacAttrStats *stats,
								AnalyzeAttrFetchFunc fetchfunc, int samplerows, double totalrows);

/*
 * range_typanalyze -- typanalyze function for range columns
 */
Datum
range_typanalyze(PG_FUNCTION_ARGS)
{
	VacAttrStats *stats = (VacAttrStats *) PG_GETARG_POINTER(0);
	TypeCacheEntry *typcache;
	Form_pg_attribute attr = stats->attr;

	/* Get information about range type; note column might be a domain */
	typcache = range_get_typcache(fcinfo, getBaseType(stats->attrtypid));

	if (attr->attstattarget < 0)
		attr->attstattarget = default_statistics_target;

	stats->compute_stats = compute_range_stats;
	stats->extra_data = typcache;
	/* same as in std_typanalyze */
	stats->minrows = 300 * attr->attstattarget;

	PG_RETURN_BOOL(true);
}

/*
 * Comparison function for sorting float8s, used for range lengths.
 */
static int
float8_qsort_cmp(const void *a1, const void *a2)
{
	const float8 *f1 = (const float8 *) a1;
	const float8 *f2 = (const float8 *) a2;

	if (*f1 < *f2)
		return -1;
	else if (*f1 == *f2)
		return 0;
	else
		return 1;
}

/*
 * Comparison function for sorting RangeBounds.
 */
static int
range_bound_qsort_cmp(const void *a1, const void *a2, void *arg)
{
	RangeBound *b1 = (RangeBound *) a1;
	RangeBound *b2 = (RangeBound *) a2;
	TypeCacheEntry *typcache = (TypeCacheEntry *) arg;

	return range_cmp_bounds(typcache, b1, b2);
}

/*
 * compute_range_stats() -- compute statistics for a range column
 */
static void
compute_range_stats(VacAttrStats *stats, AnalyzeAttrFetchFunc fetchfunc, // samplerows and totalrows looks like they represent the number of rows of
					int samplerows, double totalrows)					 // the analyzed column (from the table)
{
	TypeCacheEntry *typcache = (TypeCacheEntry *) stats->extra_data;
	bool		has_subdiff = OidIsValid(typcache->rng_subdiff_finfo.fn_oid);
	int			null_cnt = 0;
	int			non_null_cnt = 0;
	int			non_empty_cnt = 0;
	int			empty_cnt = 0;
	int			range_no;
	int			slot_idx;
	int			num_bins = stats->attr->attstattarget;
	int			num_hist;
	int 		num_dummy;
	int 		num_bucket = 100;
	Datum 		global_min_bound='+infinity';
	Datum 		global_max_bound=0;
	float8	   *lengths,
			   *dummys; /// HERE90
	RangeBound *lowers,
			   *uppers;
	double		total_width = 0;

	/* Allocate memory to hold range bounds and lengths of the sample ranges. */
	lowers = (RangeBound *) palloc(sizeof(RangeBound) * samplerows);
	uppers = (RangeBound *) palloc(sizeof(RangeBound) * samplerows);
	lengths = (float8 *) palloc(sizeof(float8) * samplerows);
	dummys = (float8 *) palloc(sizeof(float8) * samplerows); /// HERE90

	/* Loop over the sample ranges. */
	for (range_no = 0; range_no < samplerows; range_no++) // Will loop over all rows inside the (range type) column of the analyzed table. 
	{													  // Note that 'range_no' will keeps track of the current processed row.
		Datum		value; // Datum types are kind of "blobs" types : it could be an abstract way to represent any value stored in the database
		bool		isnull,
					empty;
		RangeType  *range; // Keep in mind that 'int4range' and 'int8range' are, for example, two =/= types of range ! ('range' will be used to store the type of the analyzed column + some other nebulous things that could allows it to actually store a 'range' value (ex: [2,4]))
		RangeBound	lower, // RangeBound is a struct that contains 'Datum val', 'bool infinite', 'bool inclusive' and 'bool lower'
					upper;
		float8		length;

		vacuum_delay_point();

		value = fetchfunc(stats, range_no, &isnull); // The famous "fetch" function that will retrieve 'pages' in the database. 'Stats' indicate were to look in the database. 
		if (isnull)									 // 'range_no' indicate the specific row to fetch from the DB. The return type is a 'blob-representation' of the actual row value.
		{											 // This fetch function will be assumed to make 'isnull=true' if the row doesn't contains anything
			/* range is null, just count that */
			null_cnt++;
			continue;
		}

		/*
		 * XXX: should we ignore wide values, like std_typanalyze does, to
		 * avoid bloating the statistics table?
		 */
		total_width += VARSIZE_ANY(DatumGetPointer(value)); // total_width is assumed to be increment with the size of each row content (thus is assumed to 
															// contains the size of the whole column at the end of the current 'for' loop)
		/* Get range and deserialize it for further analysis. */
		range = DatumGetRangeTypeP(value); // 'range' should contains, for some reasons, a pointer to the processed 'Datum blob' (i.e the current processed row at position 'range_no'). 
		range_deserialize(typcache, range, &lower, &upper, &empty); // [lower, upper] (empty should indicate when the current position range_no of the column contains 'empty' instead of a range)

		if (!empty) // When the current row is non-empty :
		{
			///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			if(has_subdiff){
						
				if (DatumGetFloat8(FunctionCall2Coll(&typcache->rng_subdiff_finfo,typcache->rng_collation, lower.val, global_min_bound))<0){
					//printf("lower.val-global_min_bound, %f\n",DatumGetFloat8(FunctionCall2Coll(&typcache->rng_subdiff_finfo,typcache->rng_collation, lower.val, global_min_bound)));
					global_min_bound=lower.val;
					//fflush(stdout);
				}

				if (DatumGetFloat8(FunctionCall2Coll(&typcache->rng_subdiff_finfo,typcache->rng_collation, upper.val, global_max_bound))>0){
					//printf("upper.val-global_max_bound, %f\n",DatumGetFloat8(FunctionCall2Coll(&typcache->rng_subdiff_finfo,typcache->rng_collation, upper.val, global_max_bound)));
					global_max_bound=upper.val;
					//fflush(stdout);
				}
			} 

			
							 
				

							//rng_cmp_proc_finfo
			/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

			/* Remember bounds and length for further usage in histograms */
			lowers[non_empty_cnt] = lower;										// IMPORTANT: remember, 'lowers' and 'uppers' are arrays of size 'sample row' -> The bounds value of each non-null processed range (ex. lower = 20, upper = 30 for processed range [20,30]) are stored there !  
			uppers[non_empty_cnt] = upper;

			if (lower.infinite || upper.infinite) // (note : a range-type could express an infinite range. For example: [20,infinite])
			{
				/* Length of any kind of an infinite range is infinite */
				length = get_float8_infinity();
			}
			else if (has_subdiff)
			{
				/*
				 * For an ordinary range, use subdiff function between upper
				 * and lower bound values.
				 */

				length = DatumGetFloat8(FunctionCall2Coll(&typcache->rng_subdiff_finfo, // 'length' is assumed to be 10 when a range is [20,30] or 5 when a range is [20,25] (i.e length = "upper-lower")
														  typcache->rng_collation,		// Note that the nested call offer a way to compute the difference between lower and upper !
														  upper.val, lower.val)); 
			}
			else
			{
				/* Use default value of 1.0 if no subdiff is available. */
				length = 1.0;
			}
			lengths[non_empty_cnt] = length; // The histogram of 'length' is filled with the value 'upper-lower' for each processed row 

			non_empty_cnt++;
		}
		else
			empty_cnt++;

		non_null_cnt++;
	}										
	// ################ END OF THE FOR LOOP : This is were the "fetching" process end : lowers, uppers and lengths arrays are now filled ##################
	slot_idx = 0; // Arbitrarily-chosen slot number. There are only 5 of those slots per VacAttrStats variable (see the 'stat' parameter of the function we are in)

	/* We can only compute real stats if we found some non-null values. */
	if (non_null_cnt > 0) // Rember : non_null_cnt was incremented above every time a processed row was non-null. 
	{
		Datum	   *bound_hist_values;
		Datum	   *length_hist_values;
		Datum 	   *dummy_hist_values;
		Datum 	   *equiwidth_hist_values;
		Datum 	   *equiwidth_data_values;
		int			pos,
					posfrac,
					delta,
					deltafrac,
					i;
		MemoryContext old_cxt;
		float4	   *emptyfrac;

		stats->stats_valid = true;
		/* Do the simple null-frac and width stats */
		stats->stanullfrac = (double) null_cnt / (double) samplerows; // samplerows and null_cnt are both variables computed above
		stats->stawidth = total_width / (double) non_null_cnt; // The result of the operation should gives the mean width of a row content (again, the variable was computed in the for loop above)

		/* Estimate that non-null values are unique */
		stats->stadistinct = -1.0 * (1.0 - stats->stanullfrac);

		/* Must copy the target values into anl_context */
		old_cxt = MemoryContextSwitchTo(stats->anl_context);







////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//// 1. Correctness of the current implementation of equiwidth_histogram
///		1.1 What is the difference between DatumGetFloat8(FunctionCall2Coll("substraction function")) and Datum type - Datum type ? Which one should be implemented and why ?
///	 
///	 2. Correctness of the equiwidth_data histogram
///		2.1 Which type should be specified when using a slot (if equiwidth_histogram is using float8, what type equiwidth_data should be using ? (see delta))  
///	
///	 3. Why the 10th bucket of "equiwidth histogram" is NaN ?
/// 
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	 		
		if (non_empty_cnt >= 2 && has_subdiff) 
		{

			equiwidth_hist_values = (Datum *) palloc(num_bucket*sizeof(Datum));
			equiwidth_data_values = (Datum *) palloc(num_bucket*sizeof(Datum)); // Communicating global_min_bound and global_max_bound to sel. function using histogram
			bool continuity;
			Datum delta = (global_max_bound-global_min_bound)/num_bucket;

			for (i = 0; i < non_empty_cnt; i++)
			{	
				continuity=false;
				for (int j=0; j<num_bucket; j++){
					equiwidth_data_values[j]=global_min_bound+j*delta;
					if (continuity){
						equiwidth_hist_values[j]=Float8GetDatum(DatumGetFloat8(equiwidth_hist_values[j])+1);
						if(DatumGetFloat8(FunctionCall2Coll(&typcache->rng_subdiff_finfo,typcache->rng_collation, global_min_bound+(j+1)*delta, uppers[i].val))>0){
							continuity=false;
							j=num_bucket;
						}
					} else if (DatumGetFloat8(FunctionCall2Coll(&typcache->rng_subdiff_finfo,typcache->rng_collation, global_min_bound+(j+1)*delta, lowers[i].val))>0) {
						continuity=true;
						equiwidth_hist_values[j]=Float8GetDatum(DatumGetFloat8(equiwidth_hist_values[j])+1);
					} 
				}
			}
		}
		else
		{
			dummy_hist_values = palloc(0);
			equiwidth_data_values = palloc(0);
			num_bucket = 0;
		}

		stats->staop[slot_idx] = Float8LessOperator; 
		stats->stacoll[slot_idx] = InvalidOid;
		stats->stavalues[slot_idx] = equiwidth_hist_values; 
		stats->numvalues[slot_idx] = num_bucket;
		stats->statypid[slot_idx] = FLOAT8OID; 			
		stats->statyplen[slot_idx] = sizeof(float8);	
		stats->statypbyval[slot_idx] = FLOAT8PASSBYVAL;	
		stats->statypalign[slot_idx] = 'd'; 

		/* Store the fraction of empty ranges */
		emptyfrac = (float4 *) palloc(sizeof(float4));
		*emptyfrac = ((double) empty_cnt) / ((double) non_null_cnt);
		stats->stanumbers[slot_idx] = emptyfrac;
		stats->numnumbers[slot_idx] = 1;

		stats->stakind[slot_idx] = STATISTIC_KIND_EQUIWIDTH_HISTOGRAM;
		slot_idx++; 






		stats->staop[slot_idx] = Float8LessOperator; //Note that slot_idx is now equal to 1 (see increment at line 265)
		stats->stacoll[slot_idx] = InvalidOid;
		stats->stakind[slot_idx] = STATISTIC_KIND_EQUIWIDTH_DATA; // ######################################
		stats->stavalues[slot_idx] = equiwidth_data_values; // The value of slot_idx
		stats->numvalues[slot_idx] = num_bucket; 			// indicate the slot that will be used to store the array. When looking at the definition of the type of "stats" (who is 'VacAttrStats*'),
		stats->statypid[slot_idx] = FLOAT8OID; 			// By default, postgres will assume that the value stored in those slots are arrays composed of the 
		stats->statyplen[slot_idx] = sizeof(float8);	//same type as the type of the column under analysis. Here, since we try to store float, we need 
		stats->statypbyval[slot_idx] = FLOAT8PASSBYVAL;	//to explicitely specify it
		stats->statypalign[slot_idx] = 'd'; 
		stats->stanumbers[slot_idx] = emptyfrac;
		stats->numnumbers[slot_idx] = 1;
		slot_idx++;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////::




		/*
		 * Generate a bounds histogram slot entry if there are at least two
		 * values.
		 */
		if (non_empty_cnt >= 2)
		{
			/* Sort bound values */
			qsort_arg(lowers, non_empty_cnt, sizeof(RangeBound), // IMPORTANT : The arrays lowers and uppers computed above are now sorted !
					  range_bound_qsort_cmp, typcache);
			qsort_arg(uppers, non_empty_cnt, sizeof(RangeBound),
					  range_bound_qsort_cmp, typcache);

			num_hist = non_empty_cnt; // non_empty_cnt = "samplerows - number of empty_rows"
			if (num_hist > num_bins)
				num_hist = num_bins + 1; 

			bound_hist_values = (Datum *) palloc(num_hist * sizeof(Datum)); // This will be the content of the abritrarily chosen slot '0' (cf. slot_idx) ; see below

			/*
			 * The object of this loop is to construct ranges from first and
			 * last entries in lowers[] and uppers[] along with evenly-spaced
			 * values in between. So the i'th value is a range of lowers[(i *
			 * (nvals - 1)) / (num_hist - 1)] and uppers[(i * (nvals - 1)) /
			 * (num_hist - 1)]. But computing that subscript directly risks
			 * integer overflow when the stats target is more than a couple
			 * thousand.  Instead we add (nvals - 1) / (num_hist - 1) to pos
			 * at each step, tracking the integral and fractional parts of the
			 * sum separately.
			 */
			delta = (non_empty_cnt - 1) / (num_hist - 1);
			deltafrac = (non_empty_cnt - 1) % (num_hist - 1);
			pos = posfrac = 0;

			for (i = 0; i < num_hist; i++)
			{
				bound_hist_values[i] = PointerGetDatum(range_serialize(typcache,
																	   &lowers[pos],
																	   &uppers[pos],
																	   false));
				pos += delta;
				posfrac += deltafrac;
				if (posfrac >= (num_hist - 1))
				{
					/* fractional part exceeds 1, carry to integer part */
					pos++;
					posfrac -= (num_hist - 1);
				}
			}

			stats->stakind[slot_idx] = STATISTIC_KIND_BOUNDS_HISTOGRAM; // ######################################
			stats->stavalues[slot_idx] = bound_hist_values; // The value of slot_idx
			stats->numvalues[slot_idx] = num_hist; 			// indicate the slot that will be used to store the array. When looking at the definition of the type of "stats" (who is 'VacAttrStats*'),
			slot_idx++;										// we see that 'stavalues[STATISTIC_NUM_SLOTS]' is an array initialized with '#define STATISTIC_NUM_SLOTS  5' => statvalues contains maximum 5 items (histograms) !
		}


		/*
		 * Generate a length histogram slot entry if there are at least two
		 * values.
		 */
		if (non_empty_cnt >= 2) // Repeat the idea that begin at line 217, but this time, it's the 'length_hist_values' histogram that is computed.
		{
			/*
			 * Ascending sort of range lengths for further filling of
			 * histogram
			 */
			qsort(lengths, non_empty_cnt, sizeof(float8), float8_qsort_cmp); // Again, the arrays computed during fetching (see above) are now sorted.

			num_hist = non_empty_cnt;
			if (num_hist > num_bins)
				num_hist = num_bins + 1;

			length_hist_values = (Datum *) palloc(num_hist * sizeof(Datum));

			/*
			 * The object of this loop is to copy the first and last lengths[]
			 * entries along with evenly-spaced values in between. So the i'th
			 * value is lengths[(i * (nvals - 1)) / (num_hist - 1)]. But
			 * computing that subscript directly risks integer overflow when
			 * the stats target is more than a couple thousand.  Instead we
			 * add (nvals - 1) / (num_hist - 1) to pos at each step, tracking
			 * the integral and fractional parts of the sum separately.
			 */
			delta = (non_empty_cnt - 1) / (num_hist - 1);
			deltafrac = (non_empty_cnt - 1) % (num_hist - 1);
			pos = posfrac = 0;

			for (i = 0; i < num_hist; i++)
			{
				length_hist_values[i] = Float8GetDatum(lengths[pos]);
				pos += delta;
				posfrac += deltafrac;
				if (posfrac >= (num_hist - 1))
				{
					/* fractional part exceeds 1, carry to integer part */
					pos++;
					posfrac -= (num_hist - 1);
				}
			}
		}
		else
		{
			/*
			 * Even when we don't create the histogram, store an empty array
			 * to mean "no histogram". We can't just leave stavalues NULL,
			 * because get_attstatsslot() errors if you ask for stavalues, and
			 * it's NULL. We'll still store the empty fraction in stanumbers.
			 */
			length_hist_values = palloc(0);
			num_hist = 0;
		}
		stats->staop[slot_idx] = Float8LessOperator; //Note that slot_idx is now equal to 1 (see increment at line 265)
		stats->stacoll[slot_idx] = InvalidOid;
		stats->stavalues[slot_idx] = length_hist_values; //######################################## Same idea as above
		stats->numvalues[slot_idx] = num_hist;
		stats->statypid[slot_idx] = FLOAT8OID; 			// By default, postgres will assume that the value stored in those slots are arrays composed of the 
		stats->statyplen[slot_idx] = sizeof(float8);	//same type as the type of the column under analysis. Here, since we try to store float, we need 
		stats->statypbyval[slot_idx] = FLOAT8PASSBYVAL;	//to explicitely specify it
		stats->statypalign[slot_idx] = 'd'; 

		/* Store the fraction of empty ranges */
		emptyfrac = (float4 *) palloc(sizeof(float4));
		*emptyfrac = ((double) empty_cnt) / ((double) non_null_cnt);
		stats->stanumbers[slot_idx] = emptyfrac;
		stats->numnumbers[slot_idx] = 1;

		stats->stakind[slot_idx] = STATISTIC_KIND_RANGE_LENGTH_HISTOGRAM;
		slot_idx++;









///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// DUMMY PART - Compute a dummy histogram when calling 'vacuum analyze [relname]' on a relation that contains a range-type column.


		if (non_empty_cnt >= 2) 
		{

			//qsort(dummys, non_empty_cnt, sizeof(float8), float8_qsort_cmp); 

			//num_hist = non_empty_cnt;
			//if (num_hist > num_bins)
			//	num_hist = num_bins + 1;
			num_dummy = samplerows;

			dummy_hist_values = (Datum *) palloc(num_dummy* sizeof(Datum));


			for (i = 0; i < num_dummy; i++)
			{
				dummy_hist_values[i]=Float8GetDatum(i);
				//printf("rangetypes_typanalyze.c : dummy_hist_values[%i]=%f\n",i, DatumGetFloat8(dummy_hist_values[i]));
				//fflush(stdout);
			}
		}
		else
		{
			dummy_hist_values = palloc(0);
			num_dummy = 0;
		}
		stats->staop[slot_idx] = Float8LessOperator; 
		stats->stacoll[slot_idx] = InvalidOid;
		stats->stavalues[slot_idx] = dummy_hist_values; 
		stats->numvalues[slot_idx] = num_dummy;
		stats->statypid[slot_idx] = FLOAT8OID; 			
		stats->statyplen[slot_idx] = sizeof(float8);	
		stats->statypbyval[slot_idx] = FLOAT8PASSBYVAL;	
		stats->statypalign[slot_idx] = 'd'; 

		/* Store the fraction of empty ranges */
		emptyfrac = (float4 *) palloc(sizeof(float4));
		*emptyfrac = ((double) empty_cnt) / ((double) non_null_cnt);
		stats->stanumbers[slot_idx] = emptyfrac;
		stats->numnumbers[slot_idx] = 1;

		stats->stakind[slot_idx] = STATISTIC_KIND_DUMMY; 
		slot_idx++;



///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////







		MemoryContextSwitchTo(old_cxt);
	}
	else if (null_cnt > 0)
	{
		/* We found only nulls; assume the column is entirely null */
		stats->stats_valid = true;
		stats->stanullfrac = 1.0;
		stats->stawidth = 0;	/* "unknown" */
		stats->stadistinct = 0.0;	/* "unknown" */
	}

	/*
	 * We don't need to bother cleaning up any of our temporary palloc's. The
	 * hashtable should also go away, as it used a child memory context.
	 */
}
